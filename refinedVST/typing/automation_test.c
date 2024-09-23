int main() {
}

int f_ret_expr() {
    return 1 + 2;
}

int f_temps() {
    int a = 1;
    int b = 41;
    return a + b;
}

int f_call () {
    return f_temps();
}