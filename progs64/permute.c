void permute(int* ar, int i, int j){
  int k = ar[i];
  ar[i] = ar[j];
  ar[j] = k;
}
