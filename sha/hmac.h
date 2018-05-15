
#include "sha.h"

/****specialized to use of sha256 *************/
#define HMAC_MAX_MD_CBLOCK	64 //i.e. SHA256_BLOCK_SIZE

typedef struct hmac_ctx_st
	{
	  //	EVP_MD *md; We fix this to be sha256

        SHA256_CTX md_ctx; //SHA structure for current hmac application -
         //is used for calculation of "short key", and later holds the
         //inner sha structure, to avoid overwriting i_ctx
        //unsigned char md_ctx[32]; holds short-key

        SHA256_CTX i_ctx; //the SHA structure for the inner sha application
        //unsigned char i_ctx[HMAC_MAX_MD_CBLOCK];

	SHA256_CTX o_ctx; //the SHA structure for the outer sha application
        //unsigned char o_ctx[HMAC_MAX_MD_CBLOCK];

	//unsigned int key_length;
	//unsigned char key[HMAC_MAX_MD_CBLOCK];
	} HMAC_CTX;

/***************************************************************/

void HMAC_Init(HMAC_CTX *ctx, unsigned char *key, int len);
     //final parameter fixed to SHA256, so omitted EVP_MD *md;

//Changed to match type of sha256update
//void HMAC_Update(HMAC_CTX *ctx, unsigned char *data, int len)
void HMAC_Update(HMAC_CTX *ctx, const void *data, size_t len);

void HMAC_Final(HMAC_CTX *ctx, unsigned char *md);
   //final parameter will return length of hmac-code - but its always 32,
   //so  let's omit it for now, unsigned int *len)

void HMAC_cleanup(HMAC_CTX *ctx);

unsigned char *HMAC(//fixed to SHA256: EVP_MD *evp_md,
                    unsigned char *key, int key_len, 
                    unsigned char *d, int n, 
                    unsigned char *md);
                    //always 32, unsigned int *md_len)

unsigned char *HMAC2(//fixed to SHA256: EVP_MD *evp_md,
                    unsigned char *key, int key_len, 
                    unsigned char *d, int n, 
                    unsigned char *md);
                    //always 64, unsigned int *md_len)

