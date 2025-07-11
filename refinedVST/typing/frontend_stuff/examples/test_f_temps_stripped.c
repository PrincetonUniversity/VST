int main() {
}

// spec adapated from t02_evars.c

// this "int tint" annotation would be invalid in refinedc frontend; was "int<i32>"


int f_temps() {
    int a = 1;
    return a + 41;
}