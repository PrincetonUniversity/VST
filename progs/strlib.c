char *strchr(const char *str, int c){
  for(int i = 0;; i++){
    char d = *(str + i);
    if(d == c) return (str + i);
    if(d == 0) return 0;
  }
}

char *strcpy(char *dest, const char *src){
  for(int i = 0;; i++){
    char d = *(src + i);
    *(dest + i) = d;
    if(d == 0) return dest;
  }
}

char *strcat(char *dest, const char *src){
  int i;
  for(i = 0;; i++){
    char d = *(dest + i);
    if(d == 0) break;
  }
  for(int j = 0;; j++){
    char d = *(src + j);
    *(dest + (i + j)) = d;
    if(d == 0) return dest;
  }
}

int strcmp(const char *str1, const char *str2){
  for(int i = 0;; i++){
    char d1 = *(str1 + i);
    char d2 = *(str2 + i);
    if(d1 == 0 && d2 == 0) return 0;
    else if(d1 < d2) return -1;
    else if(d1 > d2) return 1;
  }
}    
    
