//@rc::import builtins_specs from caesium

/**
 * GCC-builtins declaration.
 */
#ifndef REFINEDC_BUILTINS_SPECS_H
#define REFINEDC_BUILTINS_SPECS_H

/**
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
 *
 * This built-in function returns one plus the index of the least significant 1-bit of x,
 * or if x is zero, returns zero.
 *
 * Reference implementation: return log2(x & -x);
 */
[[rc::parameters("x : Z")]]
[[rc::args("x @ int<u64>")]]
[[rc::returns("{(Z_least_significant_one x + 1)%Z} @ int<i32>")]]
int __builtin_ffsll(unsigned long long x);

#endif
