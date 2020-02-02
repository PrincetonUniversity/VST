Require Import VST.floyd.proofauto.
Require Import stdlib. 
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
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
   FOR n:Z, gv: globals
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       (LAMBDAx [gv] [Vptrofs (Ptrofs.repr n)]
       (SEP (mem_mgr gv)))
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv;
             if eq_dec p nullval then emp
            else (malloc_token' Ews n p * memory_block Ews n p)).

Definition free_spec' :=
 DECLARE _free
   FOR n:Z, p:val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       (LAMBDAx [gv] [p]
       (SEP (mem_mgr gv;
              if eq_dec p nullval then emp
              else (malloc_token' Ews n p * memory_block Ews n p))))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).

Definition exit_spec :=
 DECLARE _exit
 FOR u: unit
 PRE [tint]
   PROP () (LAMBDAx nil [Vint (Int.one)] (SEP()))
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

Definition placeholder_spec :=
 DECLARE _placeholder
 FOR u: unit
 PRE [ ]
   PROP (False) (LAMBDAx nil nil (SEP()))
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition ispecs := [placeholder_spec].
Definition specs := [malloc_spec'; free_spec'; exit_spec].

Definition malloc_spec  {cs: compspecs} (t: type) :=
 DECLARE _malloc
   FOR gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       (LAMBDAx [gv] [Vptrofs (Ptrofs.repr (sizeof t))]
       (SEP (mem_mgr gv)))
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv;
             if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

Definition free_spec  {cs: compspecs} (t: type) :=
 DECLARE _free
   FOR p: val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       (LAMBDAx [gv] [p]
       (SEP (mem_mgr gv;
              if eq_dec p nullval then emp
              else (malloc_token Ews t p * data_at_ Ews t p))))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).

Lemma malloc_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd malloc_spec') (snd (malloc_spec t)).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split. split; auto.
intros gv.
simpl in gv. intros.
Exists (sizeof t, gv) emp.
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
{ normalize. clear H. unfold LAMBDAx, PROPx, LOCALx, SEPx, argsassert2assert. simpl; entailer!. }
 match goal with |- _ |-- prop ?PP => set (P:=PP) end.
unfold PROPx, LAMBDAx, SEPx, LOCALx, local, lift1, liftx, lift. simpl; entailer!.
subst P. normalize. intros. simpl.
apply exp_derives; intros p.
if_tac; auto. entailer!.
unfold PROPx, LOCALx, SEPx; simpl.
apply andp_derives; trivial.
apply andp_derives; trivial. entailer!.
clear - H0 H1 H2 H7.
unfold malloc_token.
assert_PROP (field_compatible t [] p).
{ entailer!.
  apply malloc_compatible_field_compatible; auto. }
entailer!.
rewrite memory_block_data_at_; auto.
Qed.

Lemma free_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd free_spec') (snd (free_spec t)).
Proof.
intros.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split. split; auto.
intros (p,gv).
simpl in gv. intros.
Exists (sizeof t, p, gv) emp.
change (liftx emp) with (@emp (environ->mpred) _ _).
rewrite !emp_sepcon.
apply andp_right.
+ if_tac.
  entailer!.
  entailer!. simpl in H0.
  unfold malloc_token. unfold LAMBDAx, argsassert2assert, PROPx, LOCALx, SEPx. simpl. entailer!.
  apply andp_derives. trivial.
  apply sepcon_derives; trivial.
  apply data_at__memory_block_cancel.
+ simpl; intros. apply prop_right.
  entailer!.
Qed.

