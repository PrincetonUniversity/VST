#include <stddef.h>

char *strchr(const char *str, int c) {
  size_t i;
  for(i = 0;; i++){
    char d = str[i];
    if(d == c) return (str + i);
    if(d == 0) return 0;
  }
}

char *strcpy(char *dest, const char *src) {
  size_t i;
  for(i = 0;; i++){
    char d = src[i];
    dest[i] = d;
    if(d == 0) return dest;
  }
}

char *strcat(char *dest, const char *src) {
  size_t i,j; char d;
  for(i = 0;; i++){
    d = dest[i];
    if(d == 0) break;
  }
  for(j = 0;; j++){
    d = src[j];
    dest[i + j] = d;
    if(d == 0) return dest;
  }
}

int strcmp(const char *str1, const char *str2) {
  size_t i;
  for(i = 0;; i++){
    char d1 = str1[i];
    char d2 = str2[i];
    if(d1 == 0 && d2 == 0) return 0;
    else if(d1 < d2) return -1;
    else if(d1 > d2) return 1;
  }
}    
    
size_t strlen(const char *str) {
  size_t i;
  for (i=0; ; i++)
    if (str[i]==0) return i;
}
