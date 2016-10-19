/* 
    Web Crawler Program 

    Program Flow:
    First, get search term from the user and build html request messages (for amazon & ebay).
    Save links to be visited in a queue and a data structure.
    Create threads for all links to be visited or maximum no. of threads.
    Then, send HTTP requests to the web servers (pulled from the queue) in parallel.
    If hostname cannot be resolved or encounters some error, move on to the next resource.
    Introduce some delay (5s) between requests to avoid misinterpreting crawler as a DOS attack.
    Collate all packets received as html dump.
    If the URL is a product page, print the html dump.
    Else, parse links (search result page and individual product pages) using regex.
    If the link is relative path, resolve to absolute path by adding protocol and domain. 
    Check if the link is already in the data structure.
    If not, add the link to the data structure.
    Repeat the process until all links have been visited.

    To compile:
        g++ -o crawler crawler.cpp -Wno-write-strings -std=gnu++11 -lsocket -lnsl -lpthread -lssl -lcrypto

    To run:
        ./tcpclient <search term>
 */

#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <strings.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <regex>
#include <set>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <pthread.h>
#include <openssl/pem.h>
#include <openssl/ssl.h>
#include <openssl/err.h>

using namespace std;

#define MAX_THREADS 200

pthread_mutex_t mutex;

const char *link_expression = "<a\\s+(?:[^>]*?\\s+)?href=\"([^\"]+)\"";

/* 
    Format: 
    <method> <path><query> HTTP/1.1\r\nHost: <host_name>\r\nReferer: <referer>\r\nConnection: close\r\n\r\n
    e.g. GET /sch/i.html?_from=R40&_trksid=m570.l1313&_nkw=shoes&_sacat=0 HTTP/1.1\r\nHost: www.ebay.com\r\nReferer: http://www.ebay.com/\r\nConnection: close\r\n\r\n
 */
char *HTTP_message_format = "GET %s HTTP/1.1\r\nHost: %s\r\nReferer: %s\r\nConnection: close\r\n\r\n"; 

/* 
    Format: 
    https://www.amazon.com/s/ref=nb_sb_noss?url=search-alias%3Daps&field-keywords=<search term>
    e.g. https://www.amazon.com/s/ref=nb_sb_noss?url=search-alias%3Daps&field-keywords=Nike+shoes
 */
char *amazon_format = "https://www.amazon.com/s/ref=nb_sb_noss?url=search-alias%3Daps&field-keywords=%s";

/* 
    Format: 
    http://www.ebay.com/sch/i.html?_from=R40&_trksid=m570.l1313&_nkw=%s&_sacat=0
    e.g. http://www.ebay.com/sch/i.html?_from=R40&_trksid=m570.l1313&_nkw=Nike+shoes&_sacat=0
 */
char *ebay_format = "http://www.ebay.com/sch/i.html?_from=R40&_trksid=m570.l1313&_nkw=%s&_sacat=0";

/* 
    Format:
    <protocol><domain><path> 
    e.g. https://www.amazon.com/  
 */
char *data_format = "%s%s%s\n";

int n_threads = 0, n_products = 0, n_results = 0;
string search_term;
FILE *fp = NULL;

unordered_set <string> links; // for checking if a web resource has been visited
unordered_set <string>::const_iterator itr;

queue<string> URLs; // for keeping web resources to visit

void error(const char *msg)
{
	perror(msg);
	exit(0);
}

void pthread_error(const char *msg)
{
	perror(msg);
	pthread_exit(NULL);
}

set<string> extract_links(string html) {
	static const regex pattern(link_expression);
	return { sregex_token_iterator(html.begin(), html.end(), pattern, 1),
		sregex_token_iterator{} };
}

/* Thread handling one particular URL */
void* clientThread ( void *args ) {
	
	/* for socket */
	struct hostent *host; 
	struct sockaddr_in server_addr; 

	/* for openssl */
	SSL_CTX *ctx;
	SSL *ssl;

	/* for multithreading */
	int rc = 0;
	void *status = NULL;

	int sock, bytes_sent, bytes_recieved, message_size, data_size;
	string url, host_name_str, path_str, referer_str;
	char *protocol = NULL, *host_name = NULL, *referer = NULL, *default_path = "/", *path = NULL, *method = "GET";
	char *send_data = NULL, *data = NULL, recv_data[1024]; // buffer for sending and receiving messages
	int port_no = 80; 
	bool https = false;

	/* get the URL this thread has been assigned to */
	url = *reinterpret_cast<string*>(args);

	if (url.find("https://") == 0) { // if url is a https link
		https = true;
		protocol = "https://";
		port_no = 443;
		url.replace(0, 8, ""); // remove "https://"
	}
	else if (url.find("http://") == 0) { // if url is a http link
		https = false;
		protocol = "http://";
		port_no = 80;
		url.replace(0, 7, ""); // remove "http://"
	}

	path_str = url.substr(url.find_first_of(default_path));
	path=(char*)malloc(strlen(path_str.c_str()) + 1);
	if(path == NULL)
		pthread_error("Error: malloc path\n");
	strcpy(path, path_str.c_str());

	host_name_str = url.substr(0, strlen(url.c_str())-strlen(path));
	host_name = (char*)malloc(strlen(host_name_str.c_str()) + 1);
	if(host_name == NULL)
		pthread_error("Error: malloc hostname\n");
	strcpy(host_name, host_name_str.c_str());

	referer_str = protocol + host_name_str + default_path;
	referer = (char*)malloc(strlen(referer_str.c_str()) + 1);
	if(referer == NULL)
		pthread_error("Error: malloc hostname\n");
	strcpy(referer, referer_str.c_str());

	/* lookup the ip address */
	if ((host = gethostbyname(host_name)) == NULL) 
		pthread_error("Error: Host name\n");

	/* initialize openssl */
	if (https) {
		SSL_load_error_strings();
		SSL_library_init ();
		OpenSSL_add_all_algorithms();

		ctx = SSL_CTX_new (TLSv1_client_method());    
		if (ctx == NULL)
			pthread_error("Error: CTX\n");
	}

	/* create a Socket structure   - "Client Socket" */
	if ((sock = socket(AF_INET, SOCK_STREAM, 0)) == -1)  
		pthread_error("Error: Socket\n");   

	/* fill in the structure */
	server_addr.sin_family = AF_INET;     
	server_addr.sin_port = htons(port_no);   
	server_addr.sin_addr = *((struct in_addr *)host->h_addr);
	bzero(&(server_addr.sin_zero),8); 

	/* connect to server at port <port_no> */
	if (connect(sock, (struct sockaddr *)&server_addr, sizeof(struct sockaddr)) == -1) 
		pthread_error("Error: Connect\n");               

	/* Start SSL negotiation. */
	if (https) {
		ssl = SSL_new (ctx);                         
		if (ssl == NULL)
			pthread_error("Error: SSL\n");  

		SSL_set_fd (ssl, sock);
		if (SSL_connect (ssl) == -1)
		{
			//Error occurred, log and close down ssl
			SSL_shutdown(ssl);
			SSL_free(ssl);
			pthread_error("Error: SSL\n");
		}
	}

	message_size = 0;
	message_size += strlen(HTTP_message_format);        /* method         */
	message_size += strlen(method);                     /* path           */
	message_size += strlen(path);                       /* headers        */
	message_size += strlen(host_name);
	message_size += strlen(referer);

	/* delay between requests */
	sleep(5); 

	/* allocate space for the message */
	send_data=(char*)malloc(message_size); 
	if(send_data == NULL)
		pthread_error("Error: malloc send_data\n");

	/* fill in the parameters for the message*/ 
	sprintf(send_data, HTTP_message_format, path, host_name, referer);
	//printf("\nRequest:\n%s", send_data);          

	/* send the request */
	if (https) 
		bytes_sent = SSL_write(ssl, send_data, strlen(send_data));
	else
		bytes_sent = send(sock, send_data, strlen(send_data), 0); 

	if (bytes_sent == -1) 
		pthread_error("Error: Send\n");


	/* receive the response */
	bool first_packet = true, crawl = true;
	int n_links = 0;
	string http_response = "";
	do { 
		/* reuse allocated memory */
		memset(recv_data, 0, sizeof(recv_data));

		if (https) 
			bytes_recieved = SSL_read(ssl, recv_data, sizeof(recv_data)); 
		else
			bytes_recieved = recv(sock, recv_data, sizeof(recv_data), 0);

		if (bytes_recieved == -1) 
			pthread_error("Error: Receive\n");

		/* store url for later use, check if it's product page or result page */
		if (first_packet) {
			data_size = strlen(data_format) + strlen(protocol) + strlen(host_name) + strlen(path);
			data = (char*)malloc(data_size);
			if(data == NULL)
				pthread_error("Error: malloc data\n");
			sprintf(data, data_format, protocol, host_name, path);
			
			url = string(data);
			if (url.find("page=") != string::npos || url.find("_pgn=") != string::npos) { // if result page
				pthread_mutex_lock(&mutex);
				n_results++;
				pthread_mutex_unlock(&mutex);
			}
			else if (url.find("&amp;keywords=") != string::npos || url.find("hash=") != string::npos) { // if product page
				pthread_mutex_lock(&mutex);
				n_products++;
				pthread_mutex_unlock(&mutex);
				crawl = false;      
			}			
			first_packet = false;
		}

		//recv_data[bytes_recieved] = '\0'; // make it null terminated
		string recv_message = string(recv_data);
		if (recv_message.find("</html>") != string::npos) 
			recv_message = recv_message.substr(0, strlen(recv_message.c_str())-strlen(recv_message.substr(recv_message.find("</html>")).c_str())+strlen("</html>"));
		http_response += recv_message; // collate http response packets

	} while (bytes_recieved > 0);

	/* jf it's not product page */
	if (crawl) {
		for (string link : extract_links(http_response)) {
			//printf("%s\n", link.c_str());
			url = "";

			if ((link.find("keywords=") != string::npos && link.find("#") == string::npos) || link.find("_pgn=") != string::npos || link.find("hash=") != string::npos) {
				if (link.find_first_of(default_path) == 0 && link.find("_pg") != string::npos) { // if link is a relative path of paginated result   
					url = protocol;
					url += host_name;
					url += link;
				} else if (link.find("ebay") != string::npos || link.find("amazon") != string::npos) // if ebay or amazon links  
					url = link;
			}

			if(url.length() > 1) { // if not empty string
				itr = links.find(url);
				if (itr == links.end()) // if not visited yet
				{
					pthread_mutex_lock(&mutex);
					//printf("%i: %s\n", thread_id, url.c_str());
					n_links++;
					URLs.push(url);
					links.emplace(url);
					pthread_mutex_unlock(&mutex);       
				} 
			}
		}
		//printf("Found %i links: %i products and %i result pages\n", n_links, n_products, n_results);
	}   
	else {
		pthread_mutex_lock(&mutex);
		printf("%s | urldelimit | %s\n", data, http_response.c_str()); 
		//fwrite(data,  sizeof(char), strlen(data), fp); 
		//fwrite(" | urldelimit | ",  sizeof(char), strlen(" | urldelimit | "), fp);
		//fwrite(http_response.c_str(),  sizeof(char), strlen(http_response.c_str()+1), fp);  
		//fwrite("\n",  sizeof(char), strlen("\n"), fp);
		pthread_mutex_unlock(&mutex); 
	} 

	// free memory allocated
	free(path);
	free(host_name);
	free(referer);
	free(send_data);
	free(data);

	path = NULL;
	host_name = NULL;
	referer = NULL;
	send_data = NULL;
	data = NULL;

	if (https) {
		SSL_shutdown (ssl);  /* send SSL/TLS close_notify */
		SSL_free (ssl);
		SSL_CTX_free (ctx);
	}

	close(sock);

	pthread_exit(NULL);

	return NULL;
}

int main(int argc,char *argv[])  //AaBee TCP Client
{        
	int rc = 0;
	void *status = NULL;

	pthread_mutex_init(&mutex, 0);

	pthread_t threadID[MAX_THREADS];     

	string url;

	int size = 0;
	char *amazon_url, *ebay_url;

	if (argc < 1) 
		error("Empty search term");

	/* get search term and replace space with "+" */
	string search_term = argv[1];
	if (argc > 1) {
		for (int i = 2; i < argc; i++) {
			search_term += "+";
			search_term += argv[i];
		}
	}

	/* get pointer to the file to be written to */
	fp = fopen("./links.txt","wb");
	if (fp == NULL) 
		error("File open");

	/* store links to be visited for retrieving later and for keeping record of visited web resources */
	size = strlen(amazon_format) + strlen(search_term.c_str()+1);
	amazon_url = (char*)malloc(size);
	sprintf(amazon_url, amazon_format, search_term.c_str());
	URLs.push(amazon_url);
	links.emplace(amazon_url);
	free(amazon_url);
	amazon_url = NULL;

	size = strlen(ebay_format) + strlen(search_term.c_str()+1);
	ebay_url = (char*)malloc(size);
	sprintf(ebay_url, ebay_format, search_term.c_str());
	URLs.push(ebay_url);
	links.emplace(ebay_url);
	free(ebay_url);
	ebay_url = NULL;

	while (!URLs.empty())
	{
		/* calculate no. of threads to be created */
		n_threads = URLs.size() > MAX_THREADS ? MAX_THREADS : URLs.size();
		
		for (int i = 0; i < n_threads; i++) {
			url = URLs.front();
			URLs.pop();
			string *URL = new string(url);

			// on a new link, create a new thread
			//  Also, tell the thread the url it should use for crawling
			if ( pthread_create ( &threadID[i] , NULL , clientThread , (void*) URL ) != 0 ) {
				//printf("Error on pthread_create()\n");
				exit(EXIT_FAILURE); 
			}
		}

		/* wait for the threads for execution */
		for (int i = 0; i < n_threads; i++) {
			rc = pthread_join(threadID[i], &status);
			if (rc) {
				//printf("Error:unable to join, %i\n", rc);
				pthread_exit(NULL);
			}   
		}  
	}

	pthread_mutex_destroy(&mutex);

	fclose (fp);             

	//printf("\nFound %i products from %i pages\n", n_products, n_results);             

	return 0;
}