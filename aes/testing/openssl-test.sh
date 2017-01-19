
echo -e -n "\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0" > tmp/16zerobytes.dat

openssl enc -aes-256-ecb -in tmp/16zerobytes.dat -K "0000000000000000000000000000000000000000000000000" -nopad | hexdump -C

# http://aes.online-domain-tools.com/


# in mbedtls/include/mbedtls/config.h, comment out
#    //#define MBEDTLS_AESNI_C

# then 

make

gcc aes_ecb_test.c -I include/ library/aes.o


