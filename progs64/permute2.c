void permute(int* ar, int i, int j);

void reverse3_using_permute() {
    int a[3] = {1, 2, 3};
    permute(a, 0, 2);  // a = {3, 2, 1}
}
