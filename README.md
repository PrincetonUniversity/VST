# Verified Software Toolchain with extensions for external reasoning

(as described in [u]Connecting Higher-Order Separation Logic with a First-Order Outside World[/u])

The definitions and theorems of the paper can be found in the following locations:

Section 2:

ghost algebras: msl/ghost.v
rules for ghost state (Figure 2): msl/ghost_seplog.v
sum ghost algebra (Definition 1) and increment example: progs/verif_incr_gen.v
positive (Definition 2) and reference (Definition 3) algebras: veric/ghost_PCM.v
safety with ghost state (Definition 5): veric/juicy_extspec.v, jsafeN_


Section 3:

rmaps with ghost state: veric/rmaps.v
Own and own assertions, basic update: veric/own.v
extended rule of consequence: veric/semax_conseq.v

Section 4:

exclusive and external-state ghost algebras: veric/ghost_PCM.v
has_ext predicate: veric/juicy_extspec.v
safety with external state: veric/juicy_extspec.v (see especially jm_bupd)

Section 5:

specifications of getchar and putchar: progs/io_specs.v
example program (Figure 5): progs/io.c, verified in progs/verif_io.v
specifications of getchars and putchars: progs/io_mem_specs.v
example program with memory (Figures 6 and 7): progs/io_mem.c, verified in progs/verif_io_mem.v

Section 6:

dry specifications of putchar/getchar and correspondence proofs: progs/io_dry.v
dry specifications of putchars/getchars and correspondence proofs (Lemma 12): progs/io_mem_dry.v
safe evolution of memory, juicy-memory reconstruction, dessicate function, juicy-dry correspondence (Definition 10), VST soundness (Theorem 11): veric/SequentialClight.v

Section 7:

CertiKOS specifications, including serial_in_spec, serial_putc_spec, etc.: progs/io_os_specs.v
consume (Definition 13), dry-syscall correspondence (Definition 14): progs/os_combine.v, consume_trace and extcalls_correct
correctness of putchar and getchar: progs/io_os_connection.v
OS safety (Definition 16), trace correctness (Lemma 17), soundness of VST + CertiKOS (Theorem 18): progs/os_combine.v, ext_safeN_trace, trace_correct, and OS_soundness
soundness of putchar + getchar (Theorem 19): progs/io_combine.v, IO_OS_soundness

Section 8:

getchar invariant (Lemma 20): progs/io_os_connection.v, stated in valid_trace, proved in sys_getc_correct
Corollary 21: progs/io_combine.v, IO_OS_ext (proof incomplete)