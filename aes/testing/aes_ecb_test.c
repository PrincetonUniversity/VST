#include <stdio.h>
#include <string.h>
#include "mbedtls/aes.h"

int main() {
    unsigned char key[32];
    unsigned char buf[16];
    mbedtls_aes_context ctx;

    memset( key, 0, 32 );
    mbedtls_aes_init( &ctx );
    memset( buf, 0, 16 );

    mbedtls_aes_setkey_enc( &ctx, key, 256 );

    mbedtls_aes_crypt_ecb( &ctx, MBEDTLS_AES_ENCRYPT, buf, buf );

    for (int i = 0; i < 16; ++i) {
        printf("%2x", buf[i]);
    }
    printf("\n");
}


