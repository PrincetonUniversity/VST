/* as far as I could determine, mutexes are 24 chars long on 32 bits,
   40 chars long on 64 bit linux machines */
/* typedef struct {char a[8]; void* b[4];} lock_t; */
typedef struct lock_t {char a[8]; void* b[6];} lock_t;

void makelock(lock_t *lock);

void freelock(lock_t *lock);

void freelock2(lock_t *lock); //for recursive locks

void acquire(lock_t *lock);

void release(lock_t *lock);

void release2(lock_t *lock); //consumes the lock

void spawn_thread(void* (*f)(void*), void* args);

void exit_thread(void);
