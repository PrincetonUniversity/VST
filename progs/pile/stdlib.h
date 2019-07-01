void *malloc(size_t);
void free(void *);
void exit(int);
size_t strlen(char *);
char *strcpy(char *, char *);
int strcmp(char *, char *);

# define assert(__e) ((__e) ? (void)0 : exit(1))
