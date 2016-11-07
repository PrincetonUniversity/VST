struct queue_t;
typedef struct queue_t queue_t;

queue_t *q_new(void);
void q_del(queue_t *tgt);
void q_add(queue_t *tgt, void *e);
void *q_tryremove(queue_t *tgt);
void *q_remove(queue_t *tgt);
