/* as far as I could determine, mutexes are 24 chars long on 32 bits,
   40 chars long on 64 bit linux machines // in fact the sizes vary greatly, just adjust them as you can */
/* typedef struct {char a[8]; void* b[4];} lock_t; */
/* typedef struct lock_t {char a[8]; void* b[4];} lock_t; //for mutex */
/* typedef struct lock_t {void* b[6];} lock_t; //for semaphore */
typedef void* lock_t[2]; //for semaphore
typedef unsigned long int thread_t; // like pthread_t
typedef int cond_t;

void makelock(void *lock);

void freelock(void *lock);

void acquire(void *lock);

void release(void *lock);

void freelock2(void *lock); //for recursive locks

void release2(void *lock); //consumes the lock

void spawn(void* (*f)(void*), void* args);

void makecond(cond_t *cond);

void freecond(cond_t *cond);

void waitcond(cond_t *cond, void *mutex);
//Pthreads only requires a mutex for wait

void signalcond(cond_t *cond);

/* For now, to abstract over the actual type used,
   all functions take void* arguments. */
