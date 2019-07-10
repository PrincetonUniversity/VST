# Verified Software Toolchain with extensions for external reasoning

(as described in _Connecting Higher-Order Separation Logic with a First-Order Outside World_)

The definitions and theorems of the paper can be found in the following locations:

Section 2:

ghost algebras: msl/ghost.v<br/>
rules for ghost state (Figure 2): msl/ghost_seplog.v<br/>
sum ghost algebra (Definition 1), increment example: progs/verif_incr_gen.v<br/>
positive (Definition 2) and reference (Definition 3) algebras: veric/ghost_PCM.v<br/>
safety with ghost state (Definition 5): veric/juicy_extspec.v, jsafeN_


Section 3:

rmaps with ghost state: veric/rmaps.v<br/>
Own and own assertions, basic update: veric/own.v<br/>
extended rule of consequence: veric/semax_conseq.v

Section 4:

exclusive and external-state ghost algebras: veric/ghost_PCM.v<br/>
has_ext predicate: veric/juicy_extspec.v<br/>
safety with external state: veric/juicy_extspec.v (see especially jm_bupd)<br/>

Section 5:

specifications of getchar and putchar: progs/io_specs.v<br/>
example program (Figure 5): progs/io.c, verified in progs/verif_io.v<br/>
specifications of getchars and putchars: progs/io_mem_specs.v<br/>
example program with memory (Figures 6 and 7): progs/io_mem.c, verified in progs/verif_io_mem.v<br/>

Section 6:

dry specifications of putchar/getchar and correspondence proofs: progs/io_dry.v<br/>
dry specifications of putchars/getchars and correspondence proofs (Lemma 12): progs/io_mem_dry.v<br/>
safe evolution of memory, juicy-memory reconstruction, dessicate function, juicy-dry correspondence (Definition 10), VST soundness (Theorem 11): veric/SequentialClight.v, mem_evolve, juicy_dry_ext_spec, whole_program_sequential_safety_ext

Section 7:

CertiKOS specifications, including serial_in_spec, serial_putc_spec, etc.: progs/io_os_specs.v<br/>
consume (Definition 13), dry-syscall correspondence (Definition 14): progs/os_combine.v, consume_trace, extcalls_correct<br/>
correctness of putchar and getchar: progs/io_os_connection.v<br/>
OS safety (Definition 16), trace correctness (Lemma 17), soundness of VST + CertiKOS (Theorem 18): progs/os_combine.v, ext_safeN_trace, trace_correct, OS_soundness<br/>
soundness of putchar + getchar (Theorem 19): progs/io_combine.v, IO_OS_soundness

Section 8:

getchar invariant (Lemma 20): progs/io_os_connection.v, stated in valid_trace, proved in sys_getc_correct<br/>
Corollary 21: progs/io_combine.v, IO_OS_ext (proof incomplete)