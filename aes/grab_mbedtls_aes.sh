#!/bin/bash
# Run this script to copy the AES files of mbed TLS to ./mbedtls

if [ -e "$1" ]; then
  rm -rf ./mbedtls
  mkdir ./mbedtls
  mkdir ./mbedtls/include
  mkdir ./mbedtls/include/mbedtls
  mkdir ./mbedtls/library
  cp $1/include/mbedtls/config.h ./mbedtls/include/mbedtls/config.h
  cp $1/include/mbedtls/check_config.h ./mbedtls/include/mbedtls/check_config.h
  cp $1/include/mbedtls/aes.h ./mbedtls/include/mbedtls/aes.h
  cp $1/library/aes.c ./mbedtls/library/aes.c
else
  echo "Usage: ./grab_mbedtls_aes.sh path_to_mbedtls"
fi

