// from https://gitlab.mpi-sws.org/iris/refinedc/-/blob/e9205970e5498df3a3d16584f17401314af65fae/tutorial/VerifyThis/t04_loops.c
#include <stddef.h>
#include "refinedc.h"

typedef struct [[rc::refined_by("xs : {list Z}")]]
[[rc::typedef("list_t : {xs <> []} @ optional<&own<...>, null>")]]
[[rc::exists("y : Z", "ys : {list Z}")]]
[[rc::constraints("{xs = y :: ys}")]]
list_node {
  [[rc::field("y @ int<i32>")]]
  int val;
  [[rc::field("ys @ list_t")]]
  struct list_node *next;
} *list_t;

list_t reverse_1(list_t l) {
  list_t reversed, tmp;
  reversed = NULL;
  while (l != NULL) {
    tmp = l->next;
    l->next = reversed;
    reversed = l;
    l = tmp;
  }
  return reversed;
}

[[rc::parameters("xs : {list Z}")]]
[[rc::args("xs @ list_t")]]
[[rc::returns("{rev xs} @ list_t")]]
list_t reverse_2(list_t l) {
  list_t reversed, tmp;
  reversed = NULL;
  [[rc::exists("l1 : {list Z}", "l2 : {list Z}")]]
  [[rc::inv_vars("reversed : l1 @ list_t", "l : l2 @ list_t")]]
  [[rc::constraints("{xs = rev l1 ++ l2}")]]
  while (l != NULL) {
    tmp = l->next;
    l->next = reversed;
    reversed = l;
    l = tmp;
  }
  return reversed;
}


[[rc::parameters("p : loc", "xs : {list Z}", "ys : {list Z}")]]
[[rc::args("p @ &own<xs @ list_t>", "ys @ list_t")]]
[[rc::ensures("own p : {xs ++ ys} @ list_t")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

void append_loop_1(list_t *l, list_t k) {
  list_t *end = l;
  while(*end != NULL) {
    end = &(*end)->next;
  }
  *end = k;
}

[[rc::parameters("p : loc", "xs : {list Z}", "ys : {list Z}")]]
[[rc::args("p @ &own<xs @ list_t>", "ys @ list_t")]]
[[rc::ensures("own p : {xs ++ ys} @ list_t")]]
void append_loop_2(list_t *l, list_t k) {
  list_t *end = l;
  [[rc::exists("pl : loc", "xs_suffix : {list Z}")]]
  [[rc::inv_vars("end : pl @ &own<xs_suffix @ list_t>")]]
  [[rc::inv_vars("l : p @ &own<wand<{pl ◁ₗ (xs_suffix ++ ys) @ list_t}, {xs ++ ys} @ list_t>>")]]
  while(*end != NULL) {
    end = &(*end)->next;
  }
  *end = k;
}