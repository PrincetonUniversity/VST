int id (int x) { return x; }

int test_id1 () {
  if (&id) return(1); else return(0);
}

int test_fptr (int (*f)(int)) {
  if (f) return(1); else return(0);
}

int test_id2 () {
    return (test_fptr (&id)); }

int test_fptr_fptr () {
  return ((&test_id1)==(&test_id2)); }

int main (){
  return (test_id1() + test_id2() + test_fptr_fptr()); 
}
