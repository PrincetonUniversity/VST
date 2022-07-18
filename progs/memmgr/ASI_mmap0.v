Require Import VST.floyd.proofauto.
 
(*Require Import mmap0. needed for function and type names but not for compspecs *)

Global Open Scope funspec_scope.

Section Mmap0_ASI.
Variable mmap0ID:ident.
Variable munmapID:ident.

Definition mmap0_spec := 
   DECLARE (*_mmap0*)mmap0ID
   WITH n:Z
   PRE [(*_addr*) (tptr tvoid), 
        (*_len*) tuint, 
(*        (*_prot*) tint,
        (*_flags*) tint,*)
        (*_fildes*) tint(*,
(*        (*_off*) tlong*) (*_off*) tint*)]
     PROP (0 <= n <= Ptrofs.max_unsigned)
     PARAMS (nullval; 
             Vptrofs (Ptrofs.repr n);
(*             Vint (Int.repr 3); (* PROT_READ|PROT_WRITE *)
             Vint (Int.repr 4098); (* MAP_PRIVATE|MAP_ANONYMOUS - platform-dependent *) *)
             Vint (Int.repr (-1))(*;
            Vlong (Int64.repr 0)Vint(Int.repr 0)*))
     GLOBALS () SEP ()
   POST [ tptr tvoid ] EX p:_, 
     PROP ( if eq_dec p nullval
            then True else malloc_compatible n p )
     LOCAL (temp ret_temp p)
     SEP ( if eq_dec p nullval
           then emp else memory_block Tsh n p).

Definition munmap_spec := 
   DECLARE (*_munmap*)munmapID
   WITH p:val, n:Z
   PRE [ (*_addr*) (tptr tvoid), 
         (*_len*) tuint ]
     PROP (0 <= n <= Ptrofs.max_unsigned)
     PARAMS (p; (Vptrofs (Ptrofs.repr n)) ) GLOBALS ()
     SEP ( memory_block Tsh n p )
   POST [ tint ] EX res: Z,
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr res)))
     SEP ( emp ).

Definition Mmap0_ASI:= [mmap0_spec; munmap_spec].
End Mmap0_ASI.