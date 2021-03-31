#include <stddef.h>

struct tree {
    unsigned int k;
    struct tree *left, *right;
};

int get_branch (struct tree * p, struct tree * p_fa){
    if (p == p_fa->left){
        return 1;
    } else {
        return 0;
    }
}