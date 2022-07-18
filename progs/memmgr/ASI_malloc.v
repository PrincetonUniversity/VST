Require Import VST.floyd.proofauto.
Require Export malloc_lemmas. (*Exports the model (constants like WA , plus lemmas)*)

(*Require Import malloc. needed for function and type names but not for compspecs 
Update: Some UPenn grad students proposed to abstract over function identifiers -
doing so in our setup makes ASIs source-program-independent!*)

Global Open Scope funspec_scope.

Record MallocTokenAPD := {
  malloc_token': share -> Z -> val -> mpred;
  malloc_token'_valid_pointer: forall sh sz p, 
      malloc_token' sh sz p |-- valid_pointer p;
  malloc_token'_local_facts:  forall sh sz p, 
      malloc_token' sh sz p |-- !! malloc_compatible sz p;
}.

Record MallocFreeAPD := {
  MF_Tok :> MallocTokenAPD;
  mem_mgr: globals -> mpred;
}.

Definition malloc_token {cs:compspecs} M (sh: share) (t: type) (p: val): mpred := 
   !! field_compatible t [] p && 
   malloc_token' M sh (sizeof t) p.

Lemma malloc_token_valid_pointer: forall {cs: compspecs} M sh t p, 
      malloc_token M sh t p |-- valid_pointer p.
Proof. intros. unfold malloc_token.
 apply andp_left2. apply malloc_token'_valid_pointer.
Qed.

#[export] Hint Resolve malloc_token'_valid_pointer : valid_pointer.
#[export] Hint Resolve malloc_token_valid_pointer : valid_pointer.

Lemma malloc_token_local_facts:  forall {cs: compspecs} M sh t p,
      malloc_token M sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold malloc_token.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply malloc_token'_local_facts.
Qed.

#[export] Hint Resolve malloc_token'_local_facts : saturate_local.
#[export] Hint Resolve malloc_token_local_facts : saturate_local.

Section Malloc_ASI.
Variable M: MallocFreeAPD.
Variable mallocID:ident.
Variable freeID:ident.

Definition malloc_spec' := 
   DECLARE (*_malloc*)mallocID
   WITH n:Z, gv:globals
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned - (WA+WORD))
       PARAMS ((Vptrofs (Ptrofs.repr n))) GLOBALS (gv)
       SEP ( mem_mgr M gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mem_mgr M gv;
             if eq_dec p nullval then emp
             else (malloc_token' M Ews n p * memory_block Ews n p)).

Definition free_spec' :=
 DECLARE (*_free*)freeID
   WITH n:Z, p:val, gv: globals
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr M gv;
            if eq_dec p nullval then emp
            else (malloc_token' M Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr M gv).

Definition Malloc_ASI:funspecs := [malloc_spec'; free_spec'].
End Malloc_ASI.

Record MallocFree_R_APD := {
  MF_Tok_R :> MallocTokenAPD;
  mem_mgr_R: resvec -> globals -> mpred; (*changed order of arguments*)
}.
(*
Definition malloc_token_R {cs:compspecs} M (sh: share) (t: type) (p: val): mpred := 
   !! field_compatible t [] p && 
   malloc_token_R' M sh (sizeof t) p.

Lemma malloc_token_R_valid_pointer: forall {cs: compspecs} M sh t p, 
      malloc_token_R M sh t p |-- valid_pointer p.
Proof. intros. unfold malloc_token.
 apply andp_left2. apply malloc_token_R'_valid_pointer.
Qed.

#[export] Hint Resolve malloc_token_R'_valid_pointer : valid_pointer.
#[export] Hint Resolve malloc_token_R_valid_pointer : valid_pointer.

Lemma malloc_token_R_local_facts:  forall {cs: compspecs} M sh t p,
      malloc_token_R M sh t p |-- !! (field_compatible t [] p /\ malloc_compatible (sizeof t) p).
Proof. intros.
 unfold malloc_token_R.
 normalize. rewrite prop_and.
 apply andp_right. apply prop_right; auto.
 apply malloc_token_R'_local_facts.
Qed.

#[export] Hint Resolve malloc_token_R'_local_facts : saturate_local.
#[export] Hint Resolve malloc_token_R_local_facts : saturate_local.
*)
Require Import VST.floyd.VSU.

Section Malloc_R_ASI.
Variable M: MallocFree_R_APD.
Variable prefillID:ident.
Variable tryprefillID:ident.
Variable mallocID:ident.
Variable freeID:ident.

Definition pre_fill_spec' :=
 DECLARE (*_pre_fill*) prefillID
   WITH n:Z, p:val, gv:globals, rvec:resvec
   PRE [ tuint, tptr tvoid ]
       PROP (0 <= n <= maxSmallChunk /\ malloc_compatible BIGBLOCK p)
       PARAMS ((Vptrofs (Ptrofs.repr n)); p) GLOBALS (gv) 
       SEP (mem_mgr_R M rvec gv; memory_block Tsh BIGBLOCK p) 
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr_R M (add_resvec rvec (size2binZ n) 
                                     (chunks_from_block (size2binZ n))) gv).

Definition try_pre_fill_spec' :=
 DECLARE (*_try_pre_fill*) tryprefillID
   WITH n:Z, req:Z, rvec:resvec, gv:globals
   PRE [ tuint, tint ]
       PROP (0 <= n <= maxSmallChunk /\ 0 <= req <= Int.max_signed)
       PARAMS ((Vint (Int.repr n)); (Vint (Int.repr req))) GLOBALS (gv) 
       SEP (mem_mgr_R M rvec gv) 
   POST [ tint ] EX result: Z,
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr result)))
     SEP (mem_mgr_R M (add_resvec rvec (size2binZ n) result) gv).

Definition malloc_spec_R' := 
   DECLARE (*_malloc*)mallocID
   WITH n:Z, gv:globals, rvec:resvec
   PRE [ size_t ]
       PROP (0 <= n <= Ptrofs.max_unsigned - (WA+WORD))
       PARAMS ((* _nbytes *) (Vptrofs (Ptrofs.repr n))) GLOBALS (gv)
       SEP ( mem_mgr_R M rvec gv)
   POST [ tptr tvoid ] EX p:_, 
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( if guaranteed rvec n
             then mem_mgr_R M (add_resvec rvec (size2binZ n) (-1)) gv *
                  malloc_token' M Ews n p * memory_block Ews n p
             else if eq_dec p nullval 
                  then mem_mgr_R M rvec gv
                  else (if n <=? maxSmallChunk 
                        then (EX rvec':_, !!(eq_except rvec' rvec (size2binZ n))
                                            && (mem_mgr_R M rvec' gv))
                        else mem_mgr_R M rvec gv) *
                       malloc_token' M Ews n p * memory_block Ews n p).

Definition free_spec_R' :=
 DECLARE (*_free*)freeID
   WITH n:Z, p:val, gv:globals, rvec:resvec
   PRE [ tptr tvoid ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr_R M rvec gv;
            if eq_dec p nullval then emp
            else (malloc_token' M Ews n p * memory_block Ews n p))
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP (if eq_dec p nullval 
            then mem_mgr_R M rvec gv
            else if n <=? maxSmallChunk
                 then mem_mgr_R M (add_resvec rvec (size2binZ n) 1) gv
                 else mem_mgr_R M rvec gv).

Definition Malloc_R_ASI:funspecs := [pre_fill_spec'; try_pre_fill_spec'; malloc_spec_R'; free_spec_R'].

Definition ForgetR:MallocFreeAPD :=
  Build_MallocFreeAPD (MF_Tok_R M) (fun gv => EX R, mem_mgr_R M R gv).

Lemma malloc_spec_R_sub i: funspec_sub (snd malloc_spec_R') (snd (malloc_spec' ForgetR i)).
Proof.
do_funspec_sub. destruct w as [n gv]. clear H.
unfold mem_mgr.
Intros rvec.
Exists (n, gv, rvec) emp. (* empty frame *)
simpl; entailer!.
intros tau ? ?. 
set (p:=eval_id ret_temp tau).
Exists p; entailer!.
destruct (guaranteed rvec n) eqn:guar.
- (* guaranteed *)
  if_tac; auto.
  Exists (add_resvec rvec (size2binZ n) (-1)); entailer!.
  rewrite H4; entailer!.
  Exists (add_resvec rvec (size2binZ n) (-1)); entailer!.
- (* not guaranteed *)
  bdestruct (n <=? maxSmallChunk).
  + if_tac; auto. Exists rvec; entailer!. Intros rvec'; Exists rvec'; entailer!.
  + if_tac; auto; Exists rvec; entailer!.
Qed.

Lemma free_spec_R_sub i: funspec_sub (snd free_spec_R') (snd (free_spec' ForgetR i)).
Proof.
do_funspec_sub. 
destruct w as [[n p] gv]. clear H.
unfold mem_mgr.
Intros rvec. Exists (n,p,gv,rvec) emp.
simpl; entailer!.
intros tau ?.
if_tac.
Exists rvec; entailer!.
bdestruct (n <=? maxSmallChunk).
- (* small *)
  Exists (add_resvec rvec (size2binZ n) 1); entailer!.
- (* large *)
  Exists rvec; entailer!.
Qed.

Variable distinctIDs: list_norepet [prefillID; tryprefillID; mallocID; freeID].

Lemma MallocASI_sqsub_MallocR_ASI: 
      funspecs_sqsub Malloc_R_ASI (Malloc_ASI ForgetR mallocID freeID).
Proof. red; intros. simpl in H.
  if_tac in H. inv H.
  { eexists; split. simpl. rewrite 2 if_false. rewrite if_true by trivial.  reflexivity.
    intros N; subst. inv distinctIDs. inv H2. apply H3. left; trivial.
    intros N; subst. inv distinctIDs. apply H1. right; left; trivial.
    apply (malloc_spec_R_sub mallocID).  }
  if_tac in H. inv H.
  { eexists; split. simpl. rewrite 3 if_false. rewrite if_true by trivial.  reflexivity.
    intros N; subst. apply H0; trivial.
    intros N; subst. inv distinctIDs. inv H3. apply H4. right; left; trivial.
    intros N; subst. inv distinctIDs. inv H3. apply H2. do 2 right; left; trivial.
    apply (free_spec_R_sub freeID). }
  congruence.
(*
  repeat (if_tac in H. [ inv H; eexists; split; [ reflexivity |] |]).
  repeat (if_tac in H; [ inv H; eexists; split; [ reflexivity |] |])
  apply malloc_spec_R_sub. apply free_spec_R_sub. congruence.*)
Qed.

End Malloc_R_ASI.