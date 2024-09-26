
#include <refinedc.h>

int main() {
}

// spec adapated from t02_evars.c
[[rc::exists("n : Z")]]
// this "int tint" annotation would be invalid in refinedc frontend; was "int<i32>"
[[rc::returns("n @ int<tint>")]]
[[rc::ensures("{n = 42}")]]
int f_temps() {
    int a = 1;
    int b = 41;
    return a + b;
}