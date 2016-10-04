#!/bin/bash
../../compcert/clightgen -I./mbedtls/include/ ./mbedtls/library/aes.c && mv ./mbedtls/library/aes.v .

