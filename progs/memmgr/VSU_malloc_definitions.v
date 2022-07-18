Require Import VST.floyd.proofauto.
Require Import ASI_mmap0.
Require Import malloc.
Require Import ASI_malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.

Definition Tok_APD := Build_MallocTokenAPD malloc_token' malloc_token'_valid_pointer
                    malloc_token'_local_facts.

Definition R_APD := Build_MallocFree_R_APD Tok_APD mem_mgr_R.

(*+ specs of private functions *)

Definition bin2size_spec :=
 DECLARE _bin2size
  WITH b: Z
  PRE [ tint ] 
     PROP( 0 <= b < BINS ) 
     PARAMS ((Vint (Int.repr b))) GLOBALS () SEP ()
  POST [ tuint ] 
     PROP() LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (bin2sizeZ b)))) SEP ().

Definition size2bin_spec :=
 DECLARE _size2bin
  WITH s: Z
  PRE [ tuint ]    
     PROP( 0 <= s <= Ptrofs.max_unsigned ) 
     PARAMS ((Vptrofs (Ptrofs.repr s))) GLOBALS () SEP ()
  POST [ tint ]
     PROP() LOCAL(temp ret_temp (Vint (Int.repr (size2binZ s)))) SEP ().


Definition list_from_block_spec :=
 DECLARE _list_from_block
  WITH s: Z, p: val, tl: val, tlen: nat, b: Z
  PRE [ tuint, tptr tschar, tptr tvoid ]    
     PROP( 0 <= b < BINS /\ s = bin2sizeZ b /\ malloc_compatible BIGBLOCK p ) 
     PARAMS ((Vptrofs (Ptrofs.repr s)); p; tl) GLOBALS ()
     SEP ( memory_block Tsh BIGBLOCK p; mmlist s tlen tl nullval )
  POST [ tptr tvoid ] EX res:_,
     PROP() 
     LOCAL(temp ret_temp res)
     SEP ( mmlist s (Z.to_nat(chunks_from_block (size2binZ s)) + tlen) res nullval * TT ).


(* The postcondition describes the list returned, together with
   TT for the wasted space at the beginning and end of the big block from mmap. *)

Definition fill_bin_spec :=
 DECLARE _fill_bin
  WITH b: _
  PRE [ tint ]
     PROP(0 <= b < BINS) PARAMS ((Vint (Int.repr b))) GLOBALS () SEP ()
  POST [ (tptr tvoid) ] EX p:_, EX len:Z,
     PROP( if eq_dec p nullval then True else len > 0 ) 
     LOCAL(temp ret_temp p)
     SEP ( if eq_dec p nullval then emp
           else mmlist (bin2sizeZ b) (Z.to_nat len) p nullval * TT).

Definition malloc_small_spec :=
   DECLARE _malloc_small
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ size_t ] 
       PROP (0 <= n <= bin2sizeZ(BINS-1))
       PARAMS ((Vptrofs (Ptrofs.repr n))) GLOBALS (gv)
       SEP ( mem_mgr_R rvec gv)
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( if guaranteed rvec n
             then mem_mgr_R (add_resvec rvec (size2binZ n) (-1)) gv *
                  malloc_token' Ews n p * memory_block Ews n p
             else if eq_dec p nullval 
                  then mem_mgr_R rvec gv
                  else (EX rvec':_, !!(eq_except rvec' rvec (size2binZ n))
                                 && mem_mgr_R rvec' gv *
                                    malloc_token' Ews n p * memory_block Ews n p) ).

Definition malloc_large_spec :=
   DECLARE _malloc_large
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ size_t ]
       PROP (bin2sizeZ(BINS-1) < n <= Ptrofs.max_unsigned - (WA+WORD))
       PARAMS ((Vptrofs (Ptrofs.repr n))) GLOBALS (gv)
       SEP ( mem_mgr_R rvec gv)
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr_R rvec gv;
            if eq_dec p nullval then emp 
            else malloc_token' Ews n p * memory_block Ews n p).

(* s is the stored chunk size and n is the original request amount. *)
(* Note: the role of n in free_small_spec is merely to facilitate proof for free itself *)
Definition free_small_spec :=
   DECLARE _free_small
   WITH p:_, s:_, n:_, gv:globals, rvec:resvec
   PRE [ tptr tvoid, tuint ]
       PROP (0 <= n <= bin2sizeZ(BINS-1) /\ s = bin2sizeZ(size2binZ n) /\ 
             malloc_compatible s p)
       PARAMS (p; (Vptrofs (Ptrofs.repr s))) GLOBALS (gv)
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            mem_mgr_R rvec gv)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr_R (add_resvec rvec (size2binZ n) 1) gv).

Definition free_large_spec :=
   DECLARE _free_large
   WITH p:_, s:_, gv:globals, rvec:resvec
   PRE [ tptr tvoid, tuint ]
       PROP (malloc_compatible s p /\ maxSmallChunk < s <= Ptrofs.max_unsigned - (WA+WORD))
       PARAMS (p; (Vptrofs (Ptrofs.repr s))) GLOBALS (gv)
       SEP ( data_at Tsh tuint (Vptrofs (Ptrofs.repr s)) (offset_val (- WORD) p); 
            data_at_ Tsh (tptr tvoid) p;
            memory_block Tsh (s - WORD) (offset_val WORD p);
            memory_block Tsh WA (offset_val (- (WA+WORD)) p);
            mem_mgr_R rvec gv)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr_R rvec gv).

Definition MF_Vprog : varspecs. mk_varspecs prog. Defined.

Definition MF_internal_specs: funspecs :=
    [malloc_large_spec; malloc_small_spec; free_large_spec; free_small_spec;
     bin2size_spec; size2bin_spec; list_from_block_spec; fill_bin_spec]
   ++ Malloc_R_ASI R_APD _pre_fill _try_pre_fill _malloc _free.

Definition MF_Imports:funspecs := Mmap0_ASI _mmap0 _munmap.

Definition MF_Gprog:funspecs := MF_Imports ++ MF_internal_specs.

Ltac start_function_hint ::= idtac. (* no hint reminder *)
