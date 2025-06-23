#include <stdlib.h>

struct test{
    int* value;
};

int main(void){
    int x = 5;
    struct test p;
    p.value = malloc(sizeof(int));
    *(p.value) = x;
    struct test* q = &p;
    while(1){
        *(q->value) = *(q->value) + 1;
        x--;
        if(x <= 0) break;
    }
    return *(p.value);
}
