char *strchr(const char *str, int c){
  for(int i = 0;; i++){
    char d = *(str + i);
    if(d == c) return (str + i);
    if(d == 0) return 0;
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
