int id (int x) { return x; }

int test_id1 () {
  if (&id) return(1); else return(0);
}

int test_fptr (int (*f)(int)) {
  if (f) return(1); else return(0);
}

int test_id2 () {
    return (test_fptr (&id)); }

int main (){
  return (test_id1() + test_id2()); 
}
