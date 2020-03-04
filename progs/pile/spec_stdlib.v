Require Import VST.floyd.proofauto.
Require Import stdlib. 
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Global Open Scope funspec_scope.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope assert.

Parameter mem_mgr: globals -> mpred.
Parameter malloc_token': share -> Z -> val -> mpred.
Parameter malloc_token'_valid_pointer: forall sh sz p, malloc_token' sh sz p |-- valid_pointer p.
Axiom make_mem_mgr: forall gv, emp |-- mem_mgr gv.

Definition malloc_token {cs: compspecs} sh t v := 
   !! field_compatible t [] v && 
   malloc_token' sh (sizeof t) v.
Lemma malloc_token_valid_pointer: forall {cs: compspecs} sh t p, malloc_token sh t p |-- valid_pointer p.
Proof. intros. unfold malloc_token.
 apply andp_left2. apply malloc_token'_valid_pointer. Qed.

Hint Resolve malloc_token'_valid_pointer : valid_pointer.
Hint Resolve malloc_token_valid_pointer : valid_pointer.

Parameter malloc_token'_local_facts:  forall sh sz p, malloc_token' sh sz p |-- !! malloc_compatible sz p.
Lemma malloc_token_local_facts:  forall {cs: compspecs} sh t p, malloc_token sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold malloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply malloc_token'_local_facts.
Qed.
Hint Resolve malloc_token'_local_facts : saturate_local.
Hint Resolve malloc_token_local_facts : saturate_local.

Definition malloc_spec' :=
 DECLARE _malloc
   WITH n:Z, gv: globals
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       PARAMS (Vptrofs (Ptrofs.repr n)) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv;
             if eq_dec p nullval then emp
            else (malloc_token' Ews n p * memory_block Ews n p)).

Definition free_spec' :=
 DECLARE _free
   WITH n:Z, p:val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv;
              if eq_dec p nullval then emp
              else (malloc_token' Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).

Definition exit_spec :=
 DECLARE _exit
 WITH i: Z
 PRE [tint]
   PROP () PARAMS (Vint (Int.repr i)) GLOBALS () SEP()
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

Definition placeholder_spec :=
 DECLARE _placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition ispecs := [placeholder_spec].
Definition specs := [malloc_spec'; free_spec'; exit_spec].

Definition malloc_spec  {cs: compspecs} (t: type) :=
 DECLARE _malloc
   WITH gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv;
             if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

Definition free_spec  {cs: compspecs} (t: type) :=
 DECLARE _free
   WITH p: val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv;
              if eq_dec p nullval then emp
              else (malloc_token Ews t p * data_at_ Ews t p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).

Lemma malloc_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd malloc_spec') (snd (malloc_spec t)).
Proof.
do_funspec_sub. rename w into gv. clear H.
Exists (sizeof t, gv) emp. simpl; entailer!.
intros tau ? ?. Exists (eval_id ret_temp tau).
entailer!.
if_tac; auto.
unfold malloc_token.
assert_PROP (field_compatible t [] (eval_id ret_temp tau)).
{ entailer!.
  apply malloc_compatible_field_compatible; auto. }
entailer!.
rewrite memory_block_data_at_; auto.
Qed.

Lemma free_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd free_spec') (snd (free_spec t)).
Proof.
do_funspec_sub. destruct w as [p gv]. clear H.
Exists (sizeof t, p, gv) emp. simpl; entailer!.
if_tac; trivial.
sep_apply data_at__memory_block_cancel.
unfold malloc_token; entailer!.
Qed.

