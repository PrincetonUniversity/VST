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
   WITH n:Z, gv: globals
   PRE [ 1%positive OF size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned)
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr n)); gvars gv)
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
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p; gvars gv)
       SEP (mem_mgr gv;
              if eq_dec p nullval then emp
              else (malloc_token' Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv).

Definition exit_spec :=
 DECLARE _exit
 WITH u: unit
 PRE [1%positive OF tint]
   PROP () LOCAL() SEP()
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

Definition placeholder_spec :=
 DECLARE _placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) LOCAL() SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition ispecs := [placeholder_spec].
Definition specs := [malloc_spec'; free_spec'; exit_spec].

Definition malloc_spec  {cs: compspecs} (t: type) :=
 DECLARE _malloc
   WITH gv: globals
   PRE [ 1%positive OF size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
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
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p; gvars gv)
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
intros.
apply NDsubsume_subsume.
split; reflexivity.
apply ESNDsubsume_NDsubsume.
split; reflexivity.
split3; auto.
split. apply compute_list_norepet_e; reflexivity.
intros gv rho rho2.
simpl in gv.
apply predicates_hered.andp_left2.
exists (sizeof t, gv), predicates_sl.emp. rewrite predicates_sl.emp_sepcon.
change (liftx emp) with (@emp (environ->mpred) _ _).
(*rewrite !emp_sepcon.*)
split.
{ destruct H as [[? ?] ?]. split; trivial. split; trivial. }
intros rho3. rewrite predicates_sl.emp_sepcon. apply predicates_hered.andp_left2.
apply predicates_hered.exp_derives; intros p.
apply predicates_hered.andp_derives; trivial.
apply predicates_hered.andp_derives; trivial.
if_tac. trivial.
unfold malloc_token. intros m [m1 [m2 [JM [M1 M2]]]]. 
rewrite sepcon_emp in M2.
exists m1, m2; split3; trivial.
rewrite sepcon_emp.
destruct M2 as [n1 [n2 [JN [N1 N2]]]]. 
assert (field_compatible t [] p).
{ destruct H as [[[? ?] [? [? ?]]] ?]. simpl in *.
  apply malloc_compatible_field_compatible; auto.
  apply malloc_token'_local_facts in N1. apply N1. }
exists n1, n2; split3; trivial.
+ split; auto.
+ rewrite memory_block_data_at_ in N2; auto. 
Qed.

Lemma free_spec_sub:
 forall {cs: compspecs} (t: type), 
   funspec_sub (snd free_spec') (snd (free_spec t)).
Proof.
intros.
apply NDsubsume_subsume.
split; reflexivity.
apply ESNDsubsume_NDsubsume.
split; reflexivity.
split3; auto.
split. apply compute_list_norepet_e; reflexivity.
intros (p,gv) rho rho2.
simpl in gv.
apply predicates_hered.andp_left2.
exists (sizeof t, p, gv), predicates_sl.emp. rewrite predicates_sl.emp_sepcon.
change (liftx emp) with (@emp (environ->mpred) _ _).
split.
{ destruct H as [? [? ?]]. split3; trivial.
  if_tac; trivial.
  eapply predicates_sl.sepcon_derives;
  [ apply predicates_hered.derives_refl | clear H1 | apply H1]; simpl.
  rewrite ! sepcon_emp.
  apply predicates_sl.sepcon_derives. 
  + unfold malloc_token. apply predicates_hered.andp_left2; trivial.
  + apply data_at__memory_block_cancel. }
intros rho3. rewrite predicates_sl.emp_sepcon. apply predicates_hered.andp_left2; trivial.
Qed.

