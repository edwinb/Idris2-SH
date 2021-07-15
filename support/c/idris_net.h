#pragma once

// Includes used by the idris-file.
#ifdef _WIN32
#include <Ws2tcpip.h>
#include <winsock2.h>
#else
#include <netdb.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/un.h>
#include <unistd.h>
#endif

struct sockaddr_storage;
struct addrinfo;

typedef struct idrnet_recv_result {
    int result;
    void *payload;
} idrnet_recv_result;

// Same type of thing as idrnet_recv_result, but for UDP, so stores some
// address information
typedef struct idrnet_recvfrom_result {
    int result;
    void *payload;
    struct sockaddr_storage *remote_addr;
} idrnet_recvfrom_result;

#ifdef _WIN32
// mingw-w64 is currently missing the afunix.h header even though windows
// supports unix sockets so we have to define the unix sockaddr structure
// ourselves
struct sockaddr_un {
    u_short sun_family;
    char sun_path[108];
};
#endif

unsigned int idrnet_peek(void *ptr, unsigned int offset);
void idrnet_poke(void *ptr, unsigned int offset, char val);

// Gets value of errno
int idrnet_errno();

int idrnet_socket(int domain, int type, int protocol);

// Address family accessors
int idrnet_af_unspec(void);
int idrnet_af_unix(void);
int idrnet_af_inet(void);
int idrnet_af_inet6(void);

// Bind
int idrnet_bind(int sockfd, int family, int socket_type, char *host, int port);

// Retrieve information about socket
int idrnet_getsockname(int sockfd, void *address, void *len);

// Connect
int idrnet_connect(int sockfd, int family, int socket_type, char *host,
                   int port);

// Accessor functions for struct_sockaddr
int idrnet_sockaddr_family(void *sockaddr);
char *idrnet_sockaddr_ipv4(void *sockaddr);
int idrnet_sockaddr_ipv4_port(void *sockaddr);
char *idrnet_sockaddr_unix(void *sockaddr);
void *idrnet_create_sockaddr();

int idrnet_sockaddr_port(int sockfd);

// Accept
int idrnet_accept(int sockfd, void *sockaddr);

// Send
int idrnet_send(int sockfd, char *data);
int idrnet_send_buf(int sockfd, void *data, int len);

// Receive
// Creates a result structure containing result and payload
void *idrnet_recv(int sockfd, int len);
// Receives directly into a buffer
int idrnet_recv_buf(int sockfd, void *buf, int len);

// UDP Send
int idrnet_sendto(int sockfd, char *data, char *host, int port, int family);
int idrnet_sendto_buf(int sockfd, void *buf, int buf_len, char *host, int port,
                      int family);

// UDP Receive
void *idrnet_recvfrom(int sockfd, int len);
void *idrnet_recvfrom_buf(int sockfd, void *buf, int len);

// Receive structure accessors
int idrnet_get_recv_res(void *res_struct);
char *idrnet_get_recv_payload(void *res_struct);
void idrnet_free_recv_struct(void *res_struct);

// Recvfrom structure accessors
int idrnet_get_recvfrom_res(void *res_struct);
char *idrnet_get_recvfrom_payload(void *res_struct);
void *idrnet_get_recvfrom_sockaddr(void *res_struct);
void idrnet_free_recvfrom_struct(void *res_struct);

int idrnet_getaddrinfo(struct addrinfo **address_res, char *host, int port,
                       int family, int socket_type);

int idrnet_geteagain();

int isNull(void *ptr);
