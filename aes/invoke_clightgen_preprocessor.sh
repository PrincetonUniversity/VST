#!/usr/bin/env bash
../../compcert/clightgen -E -I./mbedtls/include/ ./mbedtls/library/aes.c > ./aes.preprocessed.c

