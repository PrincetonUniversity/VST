#!/usr/bin/awk -f

$1 ~ /Function/ { gsub("Function ",""); print $0 }
$1 ~ /Valid/ { print ("1") }
$1 ~ /C_example/ { print ("0") }
