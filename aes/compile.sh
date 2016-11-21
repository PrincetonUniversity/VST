#!/bin/bash

cd .. # now we're in VST

COQC="coqc `cat .loadpath`"

$COQC -Q ./aes "" aes/aes.v
$COQC -Q ./aes "" aes/AES256.v
$COQC -Q ./aes "" aes/aesutils.v
$COQC -Q ./aes "" aes/mult_equiv_lemmas.v
$COQC -Q ./aes "" aes/aes_round_lemmas.v
$COQC -Q ./aes "" aes/forwarding_table_lemmas.v
$COQC -Q ./aes "" aes/verif_aes256.v

cd ./aes # go back

