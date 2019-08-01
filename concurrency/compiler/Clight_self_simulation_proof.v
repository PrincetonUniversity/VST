(* This file is old.
   New proof in : Clight_self_simulation.v
   Todo: remove once we are done with the rest.
*)


Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Clight.

Require Import VST.concurrency.compiler.self_simulation.
Require Import VST.veric.Clight_core.

Set Bullet Behavior "Strict Subproofs".

Section ClightSelfSim.

  Context (ge: genv).
  
  (*Separate state and memory*)
  Definition core:= state. (* this contains a useless memory*)
  Definition state_to_memcore st:=
    (st, get_mem st).
  Definition memcore_to_state:= set_mem .
  (* Doesn't exactly hold. 
Lemma state_to_memcore_correct:
    forall c m, state_to_memcore (memcore_to_state c m) = (c,m).
  *)  
   
  Definition memcore_to_state_correct: forall s c m,
      state_to_memcore  s = (c,m) -> s = memcore_to_state c m:=
    CC_core_CC_state_2.

Lemma is_ext_seperated j j' m m' (E:is_ext j (Mem.nextblock m) j' (Mem.nextblock m')):
  inject_separated j j' m m'.
Proof. 
  red; intros. destruct (E _ _ _ H0 H) as [? [? ?]]; split; trivial.
Qed.

Definition expr_inject (e e': expr):= e=e'.
(*
Function expr_inject (j:meminj) (e e': expr):Prop := 
  match e, e' with
  | Econst_int i t, Econst_int i' t' => i=i' /\ t=t'
  | Econst_float f t, Econst_float f' t' => f=f' /\ t=t'
  | Econst_single f t, Econst_single f' t' => f=f' /\ t=t'
  | Econst_long i t, Econst_long i' t' => i=i' /\ t=t'
  | Evar x t, Evar x' t' => x=x' /\ t=t'
  | Etempvar x t, Etempvar x' t' => x=x' /\ t=t' 
  | Ederef a t, Ederef a' t' => expr_inject j a a' /\ t=t'
  | Eaddrof a t, Eaddrof a' t' => expr_inject j a a' /\ t=t'
  | Eunop f a t, Eunop f' a' t' => expr_inject j a a' /\ t=t' /\ f=f'
  | Ebinop f a1 a2 t, Ebinop f' a1' a2' t' => expr_inject j a1 a1' /\ expr_inject j a2 a2' /\ t=t' /\ f=f'
  | Ecast a t, Ecast a' t' => expr_inject j a a' /\ t=t'
  | Efield a x t, Efield a' x' t' => expr_inject j a a' /\ t=t' /\ x=x'
  | Esizeof t1 t2, Esizeof t1' t2' => t1=t1' /\ t2=t2'
  | Ealignof t1 t2, Ealignof t1' t2' => t1=t1' /\ t2=t2'
  | _, _ => False
end.

Lemma expr_inject_type_of j: forall e e' (E: expr_inject j e e'), typeof e = typeof e'.
Proof.
induction e; destruct e'; simpl; intros; try contradiction; destruct E; subst; trivial.
destruct H0; trivial. destruct H0 as [? [? ?]]; trivial. destruct H0; trivial.
Qed.
*)
Definition exprlist_inject (*j*):= Forall2 (expr_inject (*j*)).
(*
Function stmt_inject (j:meminj) (st st':statement) {struct st}:Prop :=
  match st, st' with
  | Sskip, Skip => True
  | Sassign e1 e2, Sassign e1' e2' => expr_inject j e1 e1' /\ expr_inject j e2 e2'
  | Sset x e, Sset x' e' => x=x' /\ expr_inject j e e' 
  | Scall optid e es, Scall optid' e' es' => 
      match optid, optid' with 
        None, None => True
      | Some x, Some x' => x=x'
      | _, _ => False
      end /\ expr_inject j e e' /\ exprlist_inject j es es'
  | Sbuiltin optid ef typs es, Sbuiltin optid' ef' typs' es' =>
      match optid, optid' with   
        None, None => True   
      | Some x, Some x' => x=x'
      | _, _ => False
      end /\ ef=ef' /\ typs=typs' /\ exprlist_inject j es es'
  | Ssequence s1 s2, Ssequence s1' s2' => stmt_inject j s1 s1' /\ stmt_inject j s2 s2'
  | Sifthenelse e s1 s2, Sifthenelse e' s1' s2' => expr_inject j e e' /\ 
                         stmt_inject j s1 s1' /\ stmt_inject j s2 s2' 
  | Sloop s1 s2, Sloop s1' s2' => stmt_inject j s1 s1' /\ stmt_inject j s2 s2'
  | Sbreak, Sbreak => True 
  | Scontinue, Scontinue => True
  | Sreturn opte, Sreturn opte' => match opte, opte' with
                                    | None, None => True 
                                    | Some e, Some e' => expr_inject j e e'
                                    | _, _ => False
                                   end
  | Sswitch e ls, Sswitch e' ls' => expr_inject j e e' /\ lstmts_inject j ls ls'
  | Slabel l s, Slabel l' s' => l=l' /\ stmt_inject j s s' 
  | Sgoto l, Sgoto l' => l=l'
  | _, _ => False
  end
with lstmts_inject (j:meminj) (st st':labeled_statements) {struct st}:Prop :=
  match st, st' with
   | LSnil, LSnil => True 
   | LScons optz s ls, LScons optz' s' ls' => 
         match optz, optz' with  
           None, None => True
         | Some z, Some z' => z=z'
         | _, _ => False
         end /\ stmt_inject j s s' /\ lstmts_inject j ls ls'
   | _, _ => False
  end.
(*Check stmt_inject_ind.*)
Functional Scheme stmt_inject_indX := Induction for stmt_inject Sort Prop
with lstmts_inject_indX := Induction for lstmts_inject Sort Prop.

Check lstmts_inject_indX.
*)
Definition stmt_inject (st st':statement):=st=st'.
Definition lstmts_inject (st st':labeled_statements):=st=st'. 

Definition env_inject (j:meminj) (e e': env):Prop := 
  forall x, match PTree.get x e, PTree.get x e' with
    None, None => True
  | Some (b,t), Some (b',t') => t=t' /\ j b = Some(b',0)
  | _, _ => False
  end.

Definition tenv_inject (j:meminj) (e e': temp_env):Prop :=
  forall x, match PTree.get x e, PTree.get x e' with
    None, None => True
  | Some v, Some v' => Val.inject j v v' 
  | _, _ => False
  end.

Function cont_inject (j:meminj) (k k':cont):Prop :=
  match k, k' with
    Kstop, Kstop => True
  | Kseq s kk, Kseq s' kk' => stmt_inject (*j*) s s' /\ cont_inject j kk kk'
  | Kloop1 s1 s2 kk, Kloop1 s1' s2' kk' => stmt_inject (*j*) s1 s1' /\ 
           stmt_inject (*j*) s2 s2' /\ cont_inject j kk kk'
  | Kloop2 s1 s2 kk, Kloop2 s1' s2' kk' => stmt_inject (*j*) s1 s1' /\ 
           stmt_inject (*j*) s2 s2' /\ cont_inject j kk kk'
  | Kswitch kk, Kswitch kk' => cont_inject j kk kk'
  | Kcall optid f e te kk, Kcall optid' f' e' te' kk' =>
      match optid, optid' with
        None, None => True
      | Some x, Some x' => x=x'
      | _, _ => False
      end /\ f=f'/\ env_inject j e e' /\ tenv_inject j te te' /\ cont_inject j kk kk'
  | _, _ => False
  end.

(*
Definition code_inject (j:meminj) (st st': state): Prop:=
  match st, st' with
  | State f s k e lenv m, State f' s' k' e' lenv' m' =>
     f=f' /\ stmt_inject (*j*) s s' /\ cont_inject j k k' /\ 
     env_inject j e e' /\ tenv_inject j lenv lenv' /\ match_mem j m m'
  | Callstate fd args k m, Callstate fd' args' k' m' =>
       fd=fd' /\ Forall2 (Val.inject j) args args' /\
       cont_inject j k k' /\ match_mem j m m'
  | Returnstate r k m, Returnstate r' k' m' => Val.inject j r r' /\ cont_inject j k k' /\ match_mem j m m'
  | _, _ => False
  end. 
 *)

Definition code_inject (j:meminj) (st st': core): Prop:=
  match st, st' with
  | CC_core_State f s k e lenv, CC_core_State f' s' k' e' lenv' =>
     f=f' /\ stmt_inject (*j*) s s' /\ cont_inject j k k' /\ 
     env_inject j e e' /\ tenv_inject j lenv lenv'
  | CC_core_Callstate fd args k, CC_core_Callstate fd' args' k' =>
       fd=fd' /\ Forall2 (Val.inject j) args args' /\
       cont_inject j k k'
  | CC_core_Returnstate r k, CC_core_Returnstate r' k' => Val.inject j r r' /\ cont_inject j k k'
  | _, _ => False
  end. 

(*
Lemma expr_inject_incr j  j' (J: inject_incr j j'): forall e e' (I: expr_inject j e e'),
      expr_inject j' e e'.
Proof.
 induction e; destruct e'; simpl; intros; trivial.
 + destruct I; split; eauto.
 + destruct I; split; eauto.
 + destruct I; split; eauto.
 + destruct I as [? [? [? ?]]]; split; eauto.
 + destruct I; split; eauto.
 + destruct I as [? [? ?]]; split; eauto.
Qed.

Lemma exprlist_inject_incr j  j' (J: inject_incr j j'): forall es es' (I: exprlist_inject j es es'),
      exprlist_inject j' es es'.
Proof. 
  induction es; destruct es'; simpl; intros; inv I; constructor.
+ eapply expr_inject_incr; eauto.
+ apply IHes in H4. apply H4. 
Qed. 

Definition myPP' j' (st st': statement) (P: Prop): Prop :=
  P -> stmt_inject j' st st'.

Definition myQQ' j' (ls ls': labeled_statements) (P: Prop): Prop :=
  P -> lstmts_inject j' ls ls'.

Lemma stmt_inject_incr j: 
      forall s s', stmt_inject j s s' -> forall j', inject_incr j j' -> stmt_inject j' s s'.
Proof. intros.
apply ((stmt_inject_indX j) (myPP' j') (myQQ' j')); try red; intros; subst; simpl; trivial. 
+ destruct H1. split; eapply expr_inject_incr; eassumption.
+ destruct H1; subst; split; trivial. eapply expr_inject_incr; eassumption.
+ destruct H1 as [? [? ?]]; repeat split; trivial.
    eapply expr_inject_incr; eassumption.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1 as [? [? ?]]; repeat split; trivial.
    eapply expr_inject_incr; eassumption.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1; contradiction.
+ destruct H1 as [? [? [? ?]]]; subst; repeat split; trivial.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1 as [? [? [? ?]]]; subst; repeat split; trivial.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1; contradiction.
+ destruct H3; split; eauto.
+ destruct H3 as [? [? ?]]; repeat split; eauto. eapply expr_inject_incr; eassumption.
+ destruct H3; split; eauto.
+ eapply expr_inject_incr; eassumption.
+ contradiction. 
+ destruct H2; split. eapply expr_inject_incr; eassumption. eauto.
+ destruct H2; split; eauto.
+ contradiction.
+ destruct H3 as [? [? ?]]; repeat split; eauto.
+ destruct H3 as [? [? ?]]; repeat split; eauto.
+ destruct H3; contradiction.
+ contradiction.
Qed.
Lemma lstmt_inject_incr j: 
      (forall ls ls', lstmts_inject j ls ls' -> forall j', inject_incr j j' -> lstmts_inject j' ls ls').
Proof. intros.
apply ((lstmts_inject_indX j) (myPP' j') (myQQ' j')); try red; intros; subst; simpl; trivial. 
+ destruct H1. split; eapply expr_inject_incr; eassumption.
+ destruct H1; subst; split; trivial. eapply expr_inject_incr; eassumption.
+ destruct H1 as [? [? ?]]; repeat split; trivial.
    eapply expr_inject_incr; eassumption.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1 as [? [? ?]]; repeat split; trivial.
    eapply expr_inject_incr; eassumption.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1; contradiction.
+ destruct H1 as [? [? [? ?]]]; subst; repeat split; trivial.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1 as [? [? [? ?]]]; subst; repeat split; trivial.
    eapply exprlist_inject_incr ; eassumption.
+ destruct H1; contradiction.
+ destruct H3; split; eauto.
+ destruct H3 as [? [? ?]]; repeat split; eauto. eapply expr_inject_incr; eassumption.
+ destruct H3; split; eauto.
+ eapply expr_inject_incr; eassumption.
+ contradiction. 
+ destruct H2; split. eapply expr_inject_incr; eassumption. eauto.
+ destruct H2; split; eauto.
+ contradiction.
+ destruct H3 as [? [? ?]]; repeat split; eauto.
+ destruct H3 as [? [? ?]]; repeat split; eauto.
+ destruct H3; contradiction.
+ contradiction.
Qed.
*)
Lemma env_inject_incr j j' (J:inject_incr j j') e e' (E: env_inject j e e'): env_inject j' e e'.
Proof. red; intros.
  specialize (E x). destruct (e ! x).
+ destruct p. destruct (e' ! x); try contradiction. destruct p. destruct E; split; eauto.
+ destruct (e' ! x); trivial.
Qed.

Lemma tenv_inject_incr j j' (J:inject_incr j j') e e' (E: tenv_inject j e e'): tenv_inject j' e e'.
Proof. red; intros.
  specialize (E x). destruct (e ! x).
+ destruct (e' ! x); try contradiction. eapply val_inject_incr; eauto.
+ destruct (e' ! x); trivial.
Qed.

Lemma cont_inject_incr j j' (J:inject_incr j j'): 
      forall k k', cont_inject j k k' -> cont_inject j' k k'.
Proof. intros k.
induction k; simpl; intros. 
+ destruct k'; simpl; intros; trivial.
+ destruct k'; simpl; intros; try solve [contradiction].
  destruct H; split; eauto. (*eapply stmt_inject_incr; eauto.*)
+ destruct k'; simpl; intros; try solve [contradiction].
  destruct H as [? [? ?]]; repeat split; eauto; eapply stmt_inject_incr; eauto.
+ destruct k'; simpl; intros; try solve [contradiction].
  destruct H as [? [? ?]]; repeat split; eauto; eapply stmt_inject_incr; eauto.
+ destruct k'; simpl; intros; try solve [contradiction]. eauto.
+ destruct k'; simpl; intros; try solve [contradiction].
  destruct H as [? [? [? [? ?]]]]; subst; repeat split; eauto.
  eapply env_inject_incr; eauto.
  eapply tenv_inject_incr; eauto.
Qed.

Definition myP g e te m (a:expr) (v:val):Prop :=
  forall (j:meminj) (a':expr) (e':env) (te':temp_env) (m':mem),
     expr_inject (*j*) a a' -> env_inject j e e' -> tenv_inject j te te' ->
     Mem.inject j m m' -> exists v', eval_expr g e' te' m' a' v' /\ Val.inject j v v'.
Definition myQ g e te m (a : expr) (b : block) (i : Integers.Int.int):Prop :=
  forall (j:meminj) (a':expr) (e':env) (te':temp_env) (m':mem),
     expr_inject (*j*) a a' -> env_inject j e e' -> tenv_inject j te te' ->
     Mem.inject j m m' -> exists b' i', eval_lvalue g e' te' m' a' b' i' /\ Val.inject j (Vptr b i) (Vptr b' i').

Lemma eval_expr_lvalue_inject (g:genv) (e:env) (te:temp_env) (m:mem):
  (forall (a : expr) (v : val), eval_expr g e te m a v -> myP g e te m a v) /\
  (forall (a : expr) (b : block) (i : Integers.Int.int),
   eval_lvalue g e te m a b i -> myQ g e te m a b i).
Proof. 
apply eval_expr_lvalue_ind; intros; red; intros; simpl in *.
+ destruct a'; try contradiction; inv H.
  eexists; split; econstructor. 
+ destruct a'; try contradiction; inv H.
  eexists; split; econstructor.
+ destruct a'; try contradiction; inv H.
  eexists; split; econstructor.
+ destruct a'; try contradiction; inv H.
  eexists; split; econstructor.
+ destruct a'; try contradiction; inv H0.
  specialize (H2 i). rewrite H in H2. 
  remember (te' ! i) as u; destruct u; try contradiction.
  exists v0; split; trivial. constructor; rewrite <- Hequ; trivial.
+ destruct a'; try contradiction; inv H1.
  assert (E: expr_inject a' a'). red; trivial. 
  destruct (H0 j _ _ _ _ E H2 H3 H4) as [b' [i' [EV' INJ]]]. 
  eexists; split; eauto. 
  constructor; trivial.
+ destruct a'; try contradiction; inv H2.
  assert (E: expr_inject a' a'). red; trivial. 
(*  destruct H2 as [? [? ?]]; subst; simpl.*)
  destruct (H0 j _ _ _ _ E H3 H4 H5) as [v1' [EE I]].
  exploit Cop.sem_unary_operation_inj; try eassumption.
  - intros. eapply Mem.weak_valid_pointer_inject_val. eassumption. eassumption. econstructor; eauto.
  - intros [v' [UNOP' VINJ]].
    exists v'; split; trivial. econstructor. eassumption.
    (*rewrite <- (expr_inject_type_of _ _ _ H2);*) trivial.
+ destruct a'; try contradiction; inv H4.
  assert (A1: expr_inject a'1 a'1). red; trivial. 
  assert (A2: expr_inject a'2 a'2). red; trivial. 
(*  destruct H4 as [? [? [? ?]]]; subst; simpl.*)
  destruct (H0 j _ _ _ _ A1 H5 H6 H7) as [v1' [E1 I1]]; clear H0.
  destruct (H2 j _ _ _ _ A2 H5 H6 H7) as [v2' [E2 I2]]; clear H2.
  exploit Cop.sem_binary_operation_inj. 5: eassumption. 5: eassumption. 5: eassumption.
  - intros. eapply Mem.valid_pointer_inject_val. eassumption. eassumption. econstructor; eauto.
  - intros. eapply Mem.weak_valid_pointer_inject_val. eassumption. eassumption. econstructor; eauto.
  - intros. eapply Mem.weak_valid_pointer_inject_no_overflow. eassumption. eassumption. eassumption. 
  - intros. eapply Mem.different_pointers_inject; eauto.
  - intros [v' [BINNOP' VINJ]].
    exists v'; split; trivial. econstructor. eassumption. eassumption. eassumption.
+ destruct a'; try contradiction; inv H2.
  assert (A: expr_inject a' a'). red; trivial. 
  destruct (H0 j _ _ _ _ A H3 H4 H5) as [v1' [E1 I1]]; clear H0.
  exploit Cop.sem_cast_inj; try eassumption. 
  - intros. eapply Mem.weak_valid_pointer_inject_val. eassumption. eassumption. econstructor; eauto.
  - intros [v' [CAST' VINJ]].
    exists v'; split; trivial. econstructor. eassumption. eassumption.
+ destruct a'; try contradiction; inv H.
  eexists; split; constructor.
+ destruct a'; try contradiction; inv H.
  eexists; split; constructor.
+ destruct (H0 j _ _ _ _ H2 H3 H4 H5) as [b' [i' [EV VINJ]]]; inv H2.
  inv H1.
  - exploit Mem.loadv_inject; eauto. intros [v' [LD Vinj]].
    exists v'; split; trivial.
    econstructor. eauto. (* 
    rewrite <- (expr_inject_type_of _ _ _ H2).*) eapply deref_loc_value; eauto.
  - exists (Vptr b' i'); split; trivial.
    econstructor. eauto. (* 
    rewrite <- (expr_inject_type_of _ _ _ H2).*) eapply deref_loc_reference; eauto.
  - exists (Vptr b' i'); split; trivial.
    econstructor. eauto. (* 
    rewrite <- (expr_inject_type_of _ _ _ H2).*) eapply deref_loc_copy; eauto.
+ destruct a'; try contradiction; inv H0. 
(*  destruct H0 as [? ?]; subst; simpl.*)
  specialize (H1 i). rewrite H in H1. remember (e'!i) as q. destruct q; try contradiction.
  destruct p. (*destruct H1 as [d [? ?]]; subst.*) destruct H1 as [? ?]; subst.
  eexists; eexists; split.
  * eapply eval_Evar_local; eauto.  
  * econstructor. eassumption.  reflexivity.  
+ destruct a'; try contradiction; inv H1.
(*  destruct H1 as [? ?]; subst; simpl.*)
  specialize (H2 i). rewrite H in H2. remember (e' ! i) as q. destruct q; try contradiction.
  eexists; eexists; split. 
  - eapply eval_Evar_global; eauto. 
  - (*apply H5 in H0. econstructor; eauto.  *) admit. (*globals inject b -> b,0*) 
+ destruct a'; try contradiction; inv H1.
  assert (A: expr_inject a' a'). red; trivial.
(*  destruct H1 as [? ?]; subst; simpl.*)
  destruct (H0 _ _ _ _ _ A H2 H3 H4) as [v' [EVAL V]]. inv V.
  exists b2; eexists; split. econstructor; eauto. econstructor; eauto. 
+ destruct a'; try contradiction; inv H4.
  assert (A: expr_inject a' a'). red; trivial.
(*  destruct H4 as [? [? ?]]; subst; simpl.*)
  destruct (H0 _ _ _ _ _ A H5 H6 H7) as [v' [EVAL V]]. inv V.
  exists b2; eexists; split.
  - eapply eval_Efield_struct; eauto. 
    (*rewrite <- (expr_inject_type_of _ _ _ H4); eauto.*)
  - econstructor. eassumption. rewrite 2 Int.add_assoc. f_equal.
    rewrite Int.add_commut; trivial.
+ destruct a'; try contradiction; inv H3.
(*  destruct H3 as [? [? ?]]; subst; simpl.*)
  assert (A: expr_inject a' a'). red; trivial.
  destruct (H0 _ _ _ _ _ A H4 H5 H6) as [v' [EVAL V]]. inv V.
  exists b2; eexists; split.
  - eapply eval_Efield_union; eauto.
    (*rewrite <- (expr_inject_type_of _ _ _ H3); eauto.*)
  - econstructor; eauto.
Admitted. (*one admit, on injection of globals*)

Lemma eval_expr_inject (g:genv) e te m a v:
   eval_expr g e te m a v -> myP g e te m a v.
Proof. apply eval_expr_lvalue_inject. Qed.


Lemma eval_lvalue_inject (g:genv) e te m a b i:
   eval_lvalue g e te m a b i -> myQ g e te m a b i. 
Proof. apply eval_expr_lvalue_inject. Qed.

Lemma eval_exprlist_inject (g:genv) e te m:
  forall al tys vals (E: eval_exprlist g e te m al tys vals)
  e' te' m' al' j, env_inject j e e' -> tenv_inject j te te' ->
     Mem.inject j m m' -> exprlist_inject (*j*) al al' -> symbols_inject j g g -> (*meminj_preserves_globals g j -> *)
     exists vals', eval_exprlist g e' te' m' al' tys vals' /\ Forall2 (Val.inject j) vals vals'.
Proof.
induction al; simpl; intros; inv E.
+ inv H2. exists nil; split; constructor.
+ inv H2. rename y into a'. rename l' into al'.
  exploit eval_expr_inject; eauto. intros [v1' [E' VINJ]].
  exploit Cop.sem_cast_inject; try eassumption. 
  intros [v2' [CAST' Inj_v2]].
  exploit IHal; eauto; clear IHal. intros [vals' [EVLAS ValsInj]]. inv H8.
  eexists; split.
  econstructor; eauto.
    (*rewrite <- (expr_inject_type_of _ _ _ H8); eauto.
    eauto.*)
  constructor; trivial. 
Qed.


Lemma sem_switch_arg_inject v t n: sem_switch_arg v t = Some n ->
  forall j v', Val.inject j v v' -> sem_switch_arg v' t = Some n.
Proof. unfold sem_switch_arg. intros.
  destruct (classify_switch t); try discriminate.
+ destruct v; try contradiction; inv H. inv H0; trivial.
+ destruct v; try contradiction; inv H. inv H0; trivial.
Qed.


Definition block_inject j (z z': block * Z * Z) :=
  match z, z' with (b,lo,hi), (b',lo',hi') =>
    exists d, j b = Some (b',d) /\ lo'=lo+d /\ hi'=hi+d
  end.

Definition blocks_inject j (l l' : list (block * Z * Z)) := Forall2 (block_inject j) l l'.

Lemma freelist_inject j: forall l m m1 (FL: Mem.free_list m l = Some m1)
   m' (M: Mem.inject j m m') l' (B: blocks_inject j l l'),
   exists m1', Mem.free_list m' l' = Some m1' /\ Mem.inject j m1 m1'.
Proof.
  induction l; simpl; intros.
+ inv B. inv FL. simpl. exists m'; split; trivial.
+ destruct a as [[b lo] hi]. remember (Mem.free m b lo hi) as q.
  destruct q; try discriminate. symmetry in Heqq.
  inv B. destruct y as [[b' lo'] hi']. rename m0 into m2. rename l'0 into l'.
  destruct H1 as [d [J [LO HI]]]; subst.
  exploit Mem.free_parallel_inject. apply M. apply Heqq. apply J. 
  intros [m2' [FR' INJ2]].  
  destruct (IHl _ _ FL _ INJ2 _ H3) as [m1' [FL' INJ1]].
  exists m1'; split; trivial.
  simpl. rewrite FR'; trivial.
Qed. 

Lemma env_blocks_inject g j e e' (E: env_inject j e e'): blocks_inject j (blocks_of_env g e) (blocks_of_env g e').
Proof.
  intros.
  set (R := fun (x: (block * type)) (y: (block * type)) =>
         match x, y with
         | (b1, t1), (b2, t2) => (*exists d, j b1 = Some(b2,d) /\ t1 = t2*) j b1 = Some(b2,0) /\ t1 = t2
         end).
  assert (list_forall2
            (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements e) (PTree.elements e')).
+ apply PTree.elements_canonical_order.
  - intros id [b ty] GET. specialize (E id). rewrite GET in E. destruct (e'!id); try contradiction.
    exists p; subst; split; trivial. subst R; destruct p. destruct E; subst. (*exists 0;*) split; trivial. 
  - intros id [b sz] GET. specialize (E id). rewrite GET in E. destruct (e ! id); try contradiction.
    exists p; subst; split; trivial. subst R; destruct p. destruct E; subst. (*exists 0;*) split; trivial.
+ unfold blocks_of_env.
  generalize H. induction 1.
  - simpl. red. constructor. 
  - simpl. red. constructor.
    * unfold block_of_binding.
      destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 ty2]]. red. simpl in *. 
      destruct H0 as [? [? ?]]; subst. exists 0; repeat split; trivial. omega. 
    * apply (IHlist_forall2 H1).
Qed. 

Lemma call_cont_inject j: forall k k' (K: cont_inject j k k'), cont_inject j (call_cont k) (call_cont k').
Proof. induction k; destruct k'; simpl; intros; trivial; try contradiction.
+ destruct K. eauto.
+ destruct K as [? [? ?]]. eauto.
+ destruct K as [? [? ?]]. eauto.
+ eauto. 
Qed.

Lemma is_call_cont_inject j: forall k k' (K: cont_inject j k k') (HK: is_call_cont k), is_call_cont k'. 
Proof. induction k; destruct k'; simpl; intros; trivial. Qed.


Lemma seq_of_lbldl_stmt_inject (*j*): forall ls ls' (H: lstmts_inject (*j*) ls ls'),
   stmt_inject (*j*) (seq_of_labeled_statement ls) (seq_of_labeled_statement ls').
Proof.  
  induction ls; destruct ls'; simpl; intros; trivial; inv H; try econstructor.
(*  destruct o. 
+ destruct o0; destruct H as [? [? ?]]; try contradiction; subst. split; eauto.
+ destruct o0; destruct H as [? [? ?]]; try contradiction; subst. split; eauto.*)
Qed.
(*Proof ok but Qed fails
Lemma find_label_inject:
  forall s (*s'*) lbl k,
  match find_label lbl s k with
  | None => forall j (*(SI: stmt_inject (*j*) s s')*) k' (CI: cont_inject j k k'),
      find_label lbl s(*'*) k' = None
  | Some(s1, k1) => forall j (*(SI: stmt_inject (*j*) s s')*) k' (CI: cont_inject j k k'),
      exists (*s1'*) k1', 
         find_label lbl s(*'*) k' = Some(s1(*'*), k1') /\
         cont_inject j k1 k1' (*/\ stmt_inject (*j*) s1 s1'*)
  end

with find_label_ls_inject:
  forall ls lbl k,  
  match find_label_ls lbl ls k with
  | None => forall ls' j (LLSI: lstmts_inject (*j*) ls ls') k' (CI: cont_inject j k k'),
      find_label_ls lbl ls' k' = None
  | Some(s1, k1) => forall ls' j (LLSI: lstmts_inject (*j*) ls ls') k' (CI: cont_inject j k k'),
      exists (*s1'*) k1', 
         find_label_ls lbl ls' k' = Some(s1(*'*), k1') /\
         cont_inject j k1 k1' (*/\ stmt_inject (*j*) s1 s1'*)
  end.
Proof.
+ induction s; simpl; intros; trivial. 
  - remember (find_label lbl s1 (Kseq s2 k)) as f.
    destruct f; simpl in *; symmetry in Heqf; intros.
    * destruct p; intros. specialize (IHs1 lbl (Kseq s2 k)); rewrite Heqf in IHs1.
      destruct (IHs1 j (Kseq s2 k')) as [kk1 [FL CI1]]; clear IHs1.
      simpl; split; trivial. reflexivity.
      rewrite FL. exists kk1; auto.
    * remember (find_label lbl s2 k) as w; symmetry in Heqw; destruct w.
      ++ destruct p; intros. specialize (IHs2 lbl k); rewrite Heqw in IHs2.
         specialize (IHs1 lbl (Kseq s2 k)); rewrite Heqf in IHs1.
         rewrite (IHs1 j (Kseq s2 k')). apply (IHs2 _ _ CI). split; trivial. reflexivity.
      ++ intros. specialize (IHs2 lbl k); rewrite Heqw in IHs2.
         specialize (IHs1 lbl (Kseq s2 k)); rewrite Heqf in IHs1.
         rewrite (IHs1 j (Kseq s2 k')). apply (IHs2 _ _ CI). split; trivial. reflexivity.
  - specialize (IHs1 lbl k). 
    destruct (find_label lbl s1 k). 
    * destruct p; intros. destruct (IHs1 _ _ CI) as [kk1 [FL1 CI']]. rewrite FL1.
      exists kk1; auto.  
    * specialize (IHs2 lbl k). 
      destruct (find_label lbl s2 k).
      ++ destruct p; intros. rewrite (IHs1 _ _ CI). apply (IHs2 _ _ CI).
      ++ intros. rewrite (IHs1 _ _ CI). apply (IHs2 _ _ CI).
  - specialize (IHs1 lbl (Kloop1 s1 s2 k)). 
    destruct (find_label lbl s1 (Kloop1 s1 s2 k)). 
    * destruct p; intros. destruct (IHs1 j (Kloop1 s1 s2 k')) as [kk1 [FL1 CI']]. repeat split; trivial; reflexivity.
      rewrite FL1. exists kk1; auto.
    * specialize (IHs2 lbl (Kloop2 s1 s2 k)). 
      destruct (find_label lbl s2 (Kloop2 s1 s2 k)).
      ++ destruct p; intros. rewrite (IHs1 j). destruct (IHs2 j (Kloop2 s1 s2 k')) as [kk1 [FL1 CI']]. repeat split; trivial. 
         rewrite FL1. exists kk1; auto. repeat split; trivial. 
      ++ intros. rewrite (IHs1 j). destruct (IHs2 j (Kloop2 s1 s2 k')) as [kk1 [FL1 CI']]. repeat split; trivial. 
         trivial. repeat split; trivial.
  - specialize (find_label_ls_inject l lbl (Kswitch k)).
    destruct (find_label_ls lbl l (Kswitch k)).
    ++ destruct p; intros. apply (find_label_ls_inject _ j (eq_refl _)); simpl; trivial.
    ++ intros. apply (find_label_ls_inject _ j (eq_refl _)); simpl; trivial. 
  - destruct (AST.ident_eq lbl l); intros.
    * exists k'; auto.  
    * apply IHs. 
+ (*trivial solves the goal, but then Qed rejects the statement. So prove it by induction*)
  clear find_label_ls_inject.
  induction ls; simpl; intros. 
  - destruct ls'; inv LLSI. simpl; trivial.
  - specialize (find_label_inject s lbl (Kseq (seq_of_labeled_statement ls) k)).
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)).
    * destruct p; intros. inv LLSI. simpl.
      destruct (find_label_inject j (Kseq (seq_of_labeled_statement ls) k')) as [kk1 [FL CI1]].
        split; trivial. apply seq_of_lbldl_stmt_inject; trivial. reflexivity.
      rewrite FL. exists kk1; auto.
    * specialize (IHls lbl k). 
      destruct (find_label_ls lbl ls k).
      ++ destruct p; intros. inv LLSI; simpl.
         rewrite (find_label_inject j (Kseq (seq_of_labeled_statement ls) k')). 
           apply IHls; trivial; reflexivity. 
         split; trivial; reflexivity.
      ++ intros. inv LLSI; simpl.
         rewrite (find_label_inject j (Kseq (seq_of_labeled_statement ls) k')). 
           apply (IHls ls j); trivial; reflexivity. 
         split; trivial; reflexivity.
Admitted. (*Cannot guess decreasing argument of fix.*)*)

(*Alternative formulation, with same error during Qed:*)
Lemma find_label_inject:
  forall s (*s'*) j (*(SI: stmt_inject (*j*) s s')*) k k' (CI: cont_inject j k k') lbl,
  match find_label lbl s k with
  | None =>
      find_label lbl s(*'*) k' = None
  | Some(s1, k1) =>
      exists (*s1'*) k1', 
         find_label lbl s(*'*) k' = Some(s1(*'*), k1') /\
         cont_inject j k1 k1' (*/\ stmt_inject (*j*) s1 s1'*)
  end

with find_label_ls_inject:
  forall ls ls' j (LLSI: lstmts_inject (*j*) ls ls') k k' (CI: cont_inject j k k') lbl, 
  match find_label_ls lbl ls k with
  | None =>
      find_label_ls lbl ls' k' = None
  | Some(s1, k1) =>
      exists (*s1'*) k1', 
         find_label_ls lbl ls' k' = Some(s1(*'*), k1') /\
         cont_inject j k1 k1' (*/\ stmt_inject (*j*) s1 s1'*)
  end.
Proof.
+ clear find_label_inject. induction s; simpl; intros; trivial. 
  - exploit (IHs1 j (Kseq s2 k) (Kseq s2 k')); clear IHs1.
      simpl; split; trivial. reflexivity.
      instantiate (1:=lbl).
    remember (find_label lbl s1 (Kseq s2 k)) as f.
    destruct f; simpl in *; symmetry in Heqf; intros.
    * destruct p. destruct H as [kk1 [FL CI1]]. rewrite FL.
      exists kk1; auto.
    * rewrite H. apply (IHs2 j _ _ CI lbl).
  - specialize (IHs1 j _ _ CI lbl).
    destruct (find_label lbl s1 k). 
    * destruct p. destruct IHs1 as [kk1 [FL1 CI']]. rewrite FL1.
      exists kk1; auto.  
    * rewrite IHs1. apply (IHs2 j _ _ CI lbl). 
  - exploit (IHs1 j (Kloop1 s1 s2 k) (Kloop1 s1 s2 k')). repeat split; trivial.
    instantiate (1:=lbl). intros. 
    destruct (find_label lbl s1 (Kloop1 s1 s2 k)). 
    * destruct p. destruct H as [kk1 [FL1 CI']]. rewrite FL1.
      exists kk1; auto.  
    * rewrite H. apply (IHs2 j). simpl. repeat split; trivial.
  - eapply find_label_ls_inject. reflexivity. apply CI.
  - destruct (AST.ident_eq lbl l).
    * exists k'; auto.  
    * apply (IHs j _ _ CI lbl).
+ (*trivial solves the goal, but then Qed rejects the statement. So prove it by induction*)
  clear find_label_ls_inject.
  induction ls; simpl; intros. 
  - destruct ls'; inv LLSI. simpl; trivial.
  - destruct ls'; inv LLSI. simpl.
    remember (find_label lbl s0 (Kseq (seq_of_labeled_statement ls') k)) as q; symmetry in Heqq; destruct q.
    * exploit (find_label_inject s0 j (Kseq (seq_of_labeled_statement ls') k) (Kseq (seq_of_labeled_statement ls') k')).
        simpl; split; trivial. apply seq_of_lbldl_stmt_inject; trivial.
        reflexivity.
      instantiate (1:=lbl); rewrite Heqq. destruct p; simpl; intros [kk1 [X1 X2]]. 
      rewrite X1. exists kk1; auto.
    * remember (find_label_ls lbl ls' k) as w; symmetry in Heqw; destruct w.
      ++ destruct p. specialize (IHls ls' j (eq_refl _) _ _ CI lbl). rewrite Heqw in IHls.
         destruct IHls as [kk1 [FL CI1]]. 
         exploit (find_label_inject s0 j (Kseq (seq_of_labeled_statement ls') k) (Kseq (seq_of_labeled_statement ls') k')).
         simpl; split; trivial. apply seq_of_lbldl_stmt_inject; trivial. reflexivity.
         instantiate (1:=lbl); rewrite Heqq. intros X; rewrite X, FL. exists kk1; auto.
      ++ specialize (IHls _ j (eq_refl _) _ _ CI lbl). rewrite Heqw in IHls.
         exploit (find_label_inject s0 j (Kseq (seq_of_labeled_statement ls') k) (Kseq (seq_of_labeled_statement ls') k')).
         simpl; split; trivial. apply seq_of_lbldl_stmt_inject; trivial. reflexivity.
         instantiate (1:=lbl); rewrite Heqq. intros X; rewrite X; trivial.
Admitted. (*Cannot guess decreasing argument of fix.*)

Lemma exprlist_inject_refl: forall l, exprlist_inject l l.
Proof. induction l; econstructor. reflexivity. apply IHl. Qed.

Lemma alloc_variables_inject g: forall vars j e m e1 m1 (A:alloc_variables g e m vars e1 m1)
      e' (E:env_inject j e e') m' (M: Mem.inject j m m'),
      exists j' e1' m1', alloc_variables g e' m' vars e1' m1' /\ env_inject j' e1 e1' /\ 
                         Mem.inject j' m1 m1' /\ inject_incr j j' /\ inject_separated j j' m m'.
Proof.
induction vars; simpl; intros; inv A.
+ exists j, e', m'; split. constructor. split; trivial. split; trivial.
  split. apply inject_incr_refl. red; intros; congruence. 
+ exploit Mem.alloc_parallel_inject; eauto. instantiate (1:=0); omega. instantiate (1:=sizeof ty); apply Z.le_refl.
  intros [j' [m2' [b1' [ALLOC' [MINJ [INC [HJ' SEP]]]]]]].
  exploit (IHvars j' _ _ _ _ H6). 
  - instantiate (1:=(PTree.set id (b1', ty) e')).
    red; intros. rewrite 2 PTree.gsspec.
    destruct (peq x id); subst. split; trivial. eapply env_inject_incr; eassumption.
  - eassumption. 
  -  intros [jj' [e1' [m1' [AL' [E' [M' [INC' SEP']]]]]]].
     exists jj', e1', m1'; split. 
     * econstructor; eauto.
     * split; trivial. split; trivial.
       split. eapply inject_incr_trans; eauto.
       red; intros. specialize (SEP b0).
       destruct (eq_block b0 b1); subst.
       ++ clear SEP. specialize (INC' _ _ _ HJ'). rewrite INC' in H0; inv H0.
          split; eapply Mem.fresh_block_alloc; eauto.
       ++ rewrite <- (SEP n) in *; clear SEP n.
          destruct (SEP' _ _ _ H H0).
          split; intros N. apply H1. eapply Mem.valid_block_alloc; eassumption.
          apply H2. eapply Mem.valid_block_alloc; eassumption.
Qed.

Lemma bind_parameter_temps_inject j: forall params args l te (B: bind_parameter_temps params args l = Some te)
      args' (A: Forall2 (Val.inject j) args args') l' (L:tenv_inject j l l'),
      exists te', bind_parameter_temps params args' l' = Some te' /\ tenv_inject j te te'.
Proof. induction params; intros; inv B.
+ destruct args; inv H0. inv A. simpl. exists l'. split; trivial.
+ destruct a. destruct args. inv H0. inv A. rename y into v'. rename l'0 into args'.
  destruct (IHparams args (PTree.set i v l) te H0 _ H4 (PTree.set i v' l')) as [te' [B L']].
    red; intros. rewrite 2 PTree.gsspec.
           destruct (peq x i); subst. trivial. apply L.
  exists te'; split; trivial.
Qed. 

Lemma create_undefs_inject j l: tenv_inject j (create_undef_temps l) (create_undef_temps l).
Proof. induction l; simpl.
+ red; intros. rewrite PTree.gempty; trivial.
+ destruct a. red; intros. rewrite PTree.gsspec.
  destruct (peq x i); subst. trivial. apply IHl.
Qed. 

Lemma function_entry2_inject g f j args m e te m1 (FE: function_entry2 g f args m e te m1)
      args' (ARGS: Forall2 (Val.inject j) args args') m' (M: Mem.inject j m m'):
      exists j' e' te' m1', function_entry2 g f args' m' e' te' m1' /\ 
                            env_inject j' e e' /\ tenv_inject j' te te' /\ Mem.inject j' m1 m1' /\
                            inject_incr j j' /\ inject_separated j j' m m'.
Proof. inv FE.
exploit alloc_variables_inject; eauto.
+ instantiate (1:= empty_env). red; intros. unfold empty_env; rewrite PTree.gempty; trivial.
+ intros [j' [e1' [m1' [AL' [E' [M' [INC' SEP]]]]]]].
  exploit bind_parameter_temps_inject; eauto. apply create_undefs_inject.
  intros [te' [BP' TE']].
  exists j', e1', te', m1'; split.
  constructor; eassumption.
  split; trivial. 
  split. eapply tenv_inject_incr; eauto.
  eauto.
Qed.

Lemma alloc_variables_inject_match_mem g: forall vars j e m e1 m1 (A:alloc_variables g e m vars e1 m1)
       e' (E:env_inject j e e') m' (M: match_mem j m m'),
       exists j' e1' m1', alloc_variables g e' m' vars e1' m1' /\ env_inject j' e1 e1' /\ 
                          match_mem j' m1 m1' /\ inject_incr j j' /\ 
               is_ext j (Mem.nextblock m) j' (Mem.nextblock m') (*inject_separated j j' m m'*).
 Proof.
 induction vars; simpl; intros; inv A.
 + exists j, e', m'; split. constructor. split; trivial. split; trivial.
   split. apply inject_incr_refl. red; intros; congruence. 
 + destruct M. exploit Mem.alloc_parallel_inject; eauto. instantiate (1:=0); omega. instantiate (1:=sizeof ty); apply Z.le_refl.
   intros [j' [m2' [b1' [ALLOC' [MINJ [INC [HJ' SEP]]]]]]].
   exploit (IHvars j' _ _ _ _ H6). 
   - instantiate (1:=(PTree.set id (b1', ty) e')).
     red; intros. rewrite 2 PTree.gsspec.
     destruct (peq x id); subst. split; trivial. eapply env_inject_incr; eassumption.
   - split.
      * eassumption. 
      * red; intros. exploit Mem.perm_alloc_inv. apply H3. apply H.
        destruct (eq_block b0 b1); subst; intros. eexists; eexists; eassumption.
        apply pimage in H0. 
        rewrite (SEP _ n); trivial.
      * red; intros. exploit Mem.perm_alloc_inv. apply ALLOC'. apply H.
        destruct (eq_block b2 b1'); subst; intros.
        -- exists b1, 0, ofs_delta. split; trivial.
           split. eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eassumption. constructor. omega.
        -- clear H. destruct (ppreimage b2 _ H0) as [bb [dd [ofs [Jbb [Perm X]]]]]; subst.
           apply (Mem.perm_alloc_1 _ _ _ _ _ H3) in Perm. exists bb, dd, ofs.
           rewrite SEP; auto. 
           intros N; subst. exploit Mem.valid_block_inject_1. apply Jbb. apply minject. intros V.
            apply Mem.fresh_block_alloc in H3. contradiction. 
   -  intros [jj' [e1' [m1' [AL' [E' [M' [INC' SEP']]]]]]].
      exists jj', e1', m1'; split. 
      * econstructor; eauto.
      * split; trivial. split; trivial.
        split. eapply inject_incr_trans; eauto.
      (*Inject_separated:  red; intros. specialize (SEP b0).
        destruct (eq_block b0 b1); subst.
        ++ clear SEP. specialize (INC' _ _ _ HJ'). rewrite INC' in H0; inv H0.
           split; eapply Mem.fresh_block_alloc; eauto.
        ++ rewrite <- (SEP n) in *; clear SEP n.
           destruct (SEP' _ _ _ H H0).
           split; intros N. apply H1. eapply Mem.valid_block_alloc; eassumption.
           apply H2. eapply Mem.valid_block_alloc; eassumption.*)
      (*isext:*) red; intros. specialize (SEP b0).
        destruct (eq_block b0 b1); subst.
        ++ clear SEP. specialize (INC' _ _ _ HJ'). rewrite INC' in H; inv H.
           split; trivial. split; eapply Mem.fresh_block_alloc; eauto.
        ++ rewrite <- (SEP n) in *; clear SEP n. 
           destruct (SEP' _ _ _ H H0) as [HH1 [HH2 HH3]].
           split; trivial.
           split; intros N. apply HH2. eapply Mem.valid_block_alloc; eassumption.
           apply HH3. eapply Mem.valid_block_alloc; eassumption.
 Qed.

Lemma function_entry2_inject_match_mem g f j args m e te m1 (FE: function_entry2 g f args m e te m1)
       args' (ARGS: Forall2 (Val.inject j) args args') m' (M: match_mem j m m'):
       exists j' e' te' m1', function_entry2 g f args' m' e' te' m1' /\ 
                             env_inject j' e e' /\ tenv_inject j' te te' /\ match_mem j' m1 m1' /\
                             inject_incr j j' /\ 
            is_ext j (Mem.nextblock m) j' (Mem.nextblock m') (*inject_separated j j' m m'*).
 Proof. inv FE. 
 exploit alloc_variables_inject_match_mem; eauto.
 + instantiate (1:= empty_env). red; intros. unfold empty_env; rewrite PTree.gempty; trivial.
 + intros [j' [e1' [m1' [AL' [E' [M' [INC' SEP]]]]]]].
   exploit bind_parameter_temps_inject; eauto. apply create_undefs_inject.
   intros [te' [BP' TE']].
   exists j', e1', te', m1'; split.
   constructor; eassumption.
   split; trivial. 
   split. eapply tenv_inject_incr; eauto.
   split; eauto.
 Qed.
 
 Lemma env_inject_blocks_of_env g j e e' (E: env_inject j e e'):
   forall b lo hi, In (b, lo, hi) (blocks_of_env g e) ->
   exists b' d, In (b', lo+d, hi+d) (blocks_of_env g e') /\ j b = Some(b',d).
 Proof. apply (env_blocks_inject g) in E.
 remember (blocks_of_env g e) as l; clear Heql.
 remember (blocks_of_env g e') as l'; clear Heql'.
 induction E; simpl; intros; try contradiction.
 destruct H0; subst.
 + destruct y as [[bb loo] hii]. red in H. destruct H as [d [D [LO HI]]]. subst.
   exists bb, d; split; trivial. left; trivial.
 + destruct (IHE _ _ _ H0) as [bb [d [D J]]].
   exists bb, d; split; trivial. right; trivial.
 Qed. 
 
 Lemma env_inject_blocks_of_env_rev g j e e' (E: env_inject j e e'):
   forall b' lo' hi', In (b', lo', hi') (blocks_of_env g e') ->
   exists b d, In (b, lo'-d, hi'-d) (blocks_of_env g e) /\ j b = Some(b',d).
 Proof. apply (env_blocks_inject g) in E.
 remember (blocks_of_env g e) as l; clear Heql.
 remember (blocks_of_env g e') as l'; clear Heql'.
 induction E; simpl; intros; try contradiction.
 destruct H0; subst.
 + destruct x as [[bb loo] hii]. red in H. destruct H as [d [D [LO HI]]]. subst.
   exists bb, d; split. left; f_equal; [ f_equal | omega]. omega. trivial.
 + destruct (IHE _ _ _ H0) as [bb [d [D J]]].
   exists bb, d; split; trivial. right; trivial.
 Qed.  
 
 Lemma perm_freelist_A b ofs k p:
   forall (l : list (block * Z * Z)) m m' (FL: Mem.free_list m l = Some m')
           (P:Mem.perm m' b ofs k p),
   Mem.perm m b ofs k p /\ (forall bb lo hi, In (bb,lo,hi) l -> bb<>b \/ ofs<lo \/ hi<=ofs).
 Proof.
 induction l; simpl; intros.
 + inv FL. split; auto.
 + destruct a as ((b',lo),hi).
   remember (Mem.free m b' lo hi) as q; symmetry in Heqq; destruct q; try discriminate.
   destruct (IHl _ _ FL P) as [Q1 Q2]; clear IHl. 
   split. eapply Mem.perm_free_3; eauto.
   intros. destruct H; [inv H | apply (Q2 _ _ _ H); trivial].
   destruct (eq_block bb b); subst; [right | left; trivial].
   destruct (zlt ofs lo0); [ left; trivial | right].
   destruct (zle hi0 ofs); [ trivial | exfalso].
   apply ( Mem.perm_free_2 _ _ _ _ _ Heqq ofs k p). omega. trivial.
 Qed. 
 
 Lemma perm_freelist_B b ofs k p:
   forall (l : list (block * Z * Z)) m m' (FL: Mem.free_list m l = Some m')
          (HH: forall bb lo hi, In (bb,lo,hi) l -> bb<>b \/ ofs<lo \/ hi<=ofs)
          (P:Mem.perm m b ofs k p),
   Mem.perm m' b ofs k p.
 Proof.
 induction l; simpl; intros.
 + inv FL; trivial.
 + destruct a as ((b',lo),hi).
   remember (Mem.free m b' lo hi) as q; symmetry in Heqq; destruct q; try discriminate.
   apply (IHl _ _ FL); clear FL.
   - intros. apply HH. right; trivial.
   - eapply Mem.perm_free_1; eauto. destruct (HH b' lo hi). left; trivial. left; eauto. right; trivial.
 Qed. 
 (*
 Lemma perm_inject_freelist g j e e' (E: env_inject j e e') m m'
       (MINJ: Mem.inject j m m')
       mm (FL: Mem.free_list m (blocks_of_env g e) = Some mm)
       mm' (FL': Mem.free_list m' (blocks_of_env g e') = Some mm')
       (MMINJ: Mem.inject j mm mm') (PI: perm_inject j m m'): perm_inject j mm mm'.
 Proof. red; intros.
   destruct (PI _ _ _ H ofs p); split; intros.
 + eapply Mem.perm_inject; eassumption.
 + exploit perm_freelist_A. apply FL'. eauto. intros [P0 Q]. 
   eapply perm_freelist_B; eauto.
   intros b lo hi B. exploit env_inject_blocks_of_env; eauto.
   intros [b' [d [B' Fb]]]. specialize (Q _ _ _ B').
   destruct (eq_block b b1); subst. 
   - rewrite H in Fb; inv Fb. destruct Q as [Q | Q]. elim Q; trivial. right; omega.
   - left; trivial. 
 Qed.*)
 
 Lemma perm_preimage_freelist g j e e' (E: env_inject j e e')
       m m' (ppreimage : perm_preimage j m m')
       mm (FL:  Mem.free_list m (blocks_of_env g e) = Some mm)
       mm' (FL': Mem.free_list m' (blocks_of_env g e') = Some mm'):
       perm_preimage j mm mm'.
 Proof. red; intros.
   exploit perm_freelist_A. 2: eassumption. eassumption. intros [P B].
   destruct (ppreimage _ _ P) as [bb [dd [z [Fb [PP X]]]]]. 
   exists bb, dd, z. split; trivial. split; trivial.
   eapply perm_freelist_B; eauto. 
   intros. exploit env_inject_blocks_of_env; eauto. 
   intros [bbb [ddd [XX FF]]]. specialize (B _ _ _ XX). 
   destruct (eq_block bbb b2); subst.
   + destruct B as [BX | BX]. elim BX; trivial.
     destruct (eq_block bb0 bb); subst. rewrite FF in Fb; inv Fb. right; omega. left; trivial.
   + clear B. destruct (eq_block bb0 bb); subst.
     rewrite FF in Fb; inv Fb. elim n; trivial. left; trivial.
 Qed.
 
 Lemma match_mem_freelist g j e e' (E: env_inject j e e')
       m m' (M : match_mem j m m')
       mm (FL: Mem.free_list m (blocks_of_env g e) = Some mm)
       mm' (FL' : Mem.free_list m' (blocks_of_env g e') = Some mm')
       (INJ' : Mem.inject j mm mm'):
       match_mem j mm mm'.
 Proof.
   destruct M. split; trivial.
(* + eapply perm_inject_freelist. eassumption. apply minject. eassumption. eassumption. eassumption. eassumption.*)
 + red; intros. exploit perm_freelist_A. 2: eassumption. eassumption. intros [P B].
   eapply pimage; eauto.
 + eapply perm_preimage_freelist; eauto.
 Qed.

Lemma assign_loc_inject g:
  forall f ty m loc ofs v m' tm loc' ofs' v',
  assign_loc g ty m loc ofs v m' ->
  Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  Val.inject f v v' ->
  Mem.inject f m tm ->
  exists tm',
     assign_loc g ty tm loc' ofs' v' tm'
  /\ Mem.inject f m' tm'
  /\ (forall b chunk v,
      f b = None -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v).
Proof.
  intros. inv H.
  (* by value *)
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [A B]].
  exists tm'; split. eapply assign_loc_value; eauto. 
  split. auto.
  intros. rewrite <- H5. eapply Mem.load_store_other; eauto.
  left. inv H0. congruence.
  (* by copy *)
  inv H0. inv H1.
  rename b' into bsrc. rename ofs'0 into osrc. 
  rename loc into bdst. rename ofs into odst.
  rename loc' into bdst'. rename b2 into bsrc'.
  exploit Mem.loadbytes_length; eauto. intros LEN. 
  destruct (zeq (@sizeof g ty) 0).
  { rewrite e in *. simpl in *. rewrite Mem.loadbytes_empty in H7; [inv H7 |omega].
    exploit Mem.storebytes_mapped_inject. apply H2. apply H8. eassumption. constructor. intros [m2' [ST2 M2']].
    clear H4 H5. 
    exists m2'; split.
    + apply assign_loc_copy with (bytes:=nil); eauto; intros; try omega.
      - rewrite e, ! Zplus_0_r in *. 
        destruct (eq_block bsrc' bdst'); subst; [ right | left; trivial].
        destruct (zeq (Int.unsigned (Int.add osrc (Int.repr delta0)))
                      (Int.unsigned (Int.add odst (Int.repr delta)))); [ left; trivial | right].
        destruct (zle (Int.unsigned (Int.add osrc (Int.repr delta0)))
                       (Int.unsigned (Int.add odst (Int.repr delta)))); [ left; trivial | right]. 
        destruct (zle (Int.unsigned (Int.add odst (Int.repr delta)))
                      (Int.unsigned (Int.add osrc (Int.repr delta0)))); [ trivial | omega].
      - rewrite e, Mem.loadbytes_empty. trivial. omega. 
      - rewrite Int.add_unsigned, 2 Int.unsigned_repr; trivial. admit. admit. (*storebytes nil*)  (*rewrite Int.add_unsigned. rewrite 2 Int.unsigned_repr. trivial. inv H2. inv mi_inj.
    apply Mem.storebytes_nil.
    exploit Mem.disjoint_or_equal_inject. apply H2. apply H9. apply H11.
     instantiate (1:=Int.unsigned osrc).  with (m := m); eauto.
      apply Mem.range_perm_max with Cur; auto.
    apply Mem.range_perm_max with Cur; auto.*)
    + split; trivial.
      intros . rewrite <- H0. eapply mem_lemmas.load_storebytes_nil. apply H8. }
    
  assert (SZPOS: @sizeof g ty > 0) by (specialize (@sizeof_pos g ty); intros; omega). 
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + @sizeof g ty) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + @sizeof g ty) Cur Nonempty).
    replace (@sizeof g ty) with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega. 
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
  exists tm'. 
  split.
- eapply assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto; intros.
  * apply H4 in H. eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_blockcopy_1248.
    apply sizeof_alignof_blockcopy_compat. 
  * apply H5 in H. eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_blockcopy_1248.
    apply sizeof_alignof_blockcopy_compat. 
  * eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
    apply Mem.range_perm_max with Cur; auto.
    apply Mem.range_perm_max with Cur; auto.
- split. auto.
  intros. rewrite <- H0. eapply Mem.load_storebytes_other; eauto. 
  left. congruence.
Admitted. (*all admits are bout storebytes nil*)

Lemma assign_loc_inject_match_mem g:
  forall f ty m loc ofs v m' tm loc' ofs' v',
  assign_loc g ty m loc ofs v m' ->
  Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  Val.inject f v v' ->
  match_mem f m tm ->
  exists tm',
     assign_loc g ty tm loc' ofs' v' tm'
  /\ match_mem f m' tm'
  /\ (forall b chunk v,
      f b = None -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v).
Proof.
  intros. inv H. inv H2.
+ (* by value *)
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [A B]].
  exists tm'; split. eapply assign_loc_value; eauto. 
  split. 
  - split; auto.
    * red; intros. eapply pimage. eapply Mem.perm_store_2; eauto.
    * red; intros. exploit Mem.perm_store_2. 2: eassumption. eassumption. intros.
      exploit ppreimage. apply H2. intros [b [d [z [Fb [P X]]]]].
      exists b, d, z. split; trivial. split; trivial. eapply Mem.perm_store_1; eauto.
  - intros. rewrite <- H2. eapply Mem.load_store_other; eauto.
    left. inv H0. congruence.
+ (* by copy *)
  inv H0. inv H1. destruct H2.
  rename b' into bsrc. rename ofs'0 into osrc. 
  rename loc into bdst. rename ofs into odst.
  rename loc' into bdst'. rename b2 into bsrc'.
  exploit Mem.loadbytes_length; eauto. intros LEN. 
  destruct (zeq (@sizeof g ty) 0).
  { rewrite e in *. simpl in *. clear H4 H5. (* destruct ty; simpl in *; try omega; try discriminate. destruct i; omega. destruct f0; omega. admit.  Print composite. co_sizeof. simpl in *. inv H3. unfold sizeof in e.*)
    rewrite Mem.loadbytes_empty in H7; [inv H7 |omega].
    exploit Mem.storebytes_mapped_inject. apply minject. apply H8. eassumption. constructor. intros [m2' [ST2 M2']].
    exists m2'; split.
    + apply assign_loc_copy with (bytes:=nil); eauto; intros; try omega.
      - rewrite e, ! Zplus_0_r in *. 
        destruct (eq_block bsrc' bdst'); subst; [ right | left; trivial].
        destruct (zeq (Int.unsigned (Int.add osrc (Int.repr delta0)))
                      (Int.unsigned (Int.add odst (Int.repr delta)))); [ left; trivial | right].
        destruct (zle (Int.unsigned (Int.add osrc (Int.repr delta0)))
                       (Int.unsigned (Int.add odst (Int.repr delta)))); [ left; trivial | right]. 
        destruct (zle (Int.unsigned (Int.add odst (Int.repr delta)))
                      (Int.unsigned (Int.add osrc (Int.repr delta0)))); [ trivial | omega].
      - rewrite e, Mem.loadbytes_empty. trivial. omega. 
      - rewrite Int.add_unsigned, 2 Int.unsigned_repr; trivial.  admit. admit. (*storebytes nil*)  (*rewrite Int.add_unsigned. rewrite 2 Int.unsigned_repr. trivial. inv H2. inv mi_inj.
    apply Mem.storebytes_nil.
    exploit Mem.disjoint_or_equal_inject. apply H2. apply H9. apply H11.
     instantiate (1:=Int.unsigned osrc).  with (m := m); eauto.
      apply Mem.range_perm_max with Cur; auto.
    apply Mem.range_perm_max with Cur; auto.*)
    + split.
      - split. * trivial.
        * red; intros. eapply pimage. eapply Mem.perm_storebytes_2; eauto.
        * red; intros. exploit Mem.perm_storebytes_2. 2: eassumption. eassumption. intros.
          exploit ppreimage. apply H0. intros [b [d [z [Fb [P X]]]]].
          exists b, d, z. split; trivial. split; trivial. eapply Mem.perm_storebytes_1; eauto.
      - intros. rewrite <- H0. eapply mem_lemmas.load_storebytes_nil. apply H8. }
    
  assert (SZPOS: @sizeof g ty > 0) by (specialize (@sizeof_pos g ty); intros; omega). 
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + @sizeof g ty) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + @sizeof g ty) Cur Nonempty).
    replace (@sizeof g ty) with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega. 
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
  exists tm'. 
  split.
- eapply assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto; intros.
  * apply H4 in H. eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_blockcopy_1248.
    apply sizeof_alignof_blockcopy_compat. 
  * apply H5 in H. eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_blockcopy_1248.
    apply sizeof_alignof_blockcopy_compat. 
  * eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
    apply Mem.range_perm_max with Cur; auto.
    apply Mem.range_perm_max with Cur; auto.
- split.
  * split. ++ trivial.
      ++ red; intros. eapply pimage. eapply Mem.perm_storebytes_2; eauto.
      ++ red; intros. exploit Mem.perm_storebytes_2. 2: eassumption. eassumption. intros.
          exploit ppreimage. apply H0. intros [b [d [z [Fb [P X]]]]].
          exists b, d, z. split; trivial. split; trivial. eapply Mem.perm_storebytes_1; eauto.
  * intros. rewrite <- H0. eapply Mem.load_storebytes_other; eauto. 
    left. congruence.
Admitted. (*all admits are about storebytes nil*) 

Axiom external_call_match_mem_inject:
  forall (ef : AST.external_function) (ge1 ge2 : Senv.t)
         (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem)
         (f : block -> option (block * Z)) (m1' : mem) (vargs' : list val),
       symbols_inject f ge1 ge2 ->
       external_call ef ge1 vargs m1 t vres m2 ->
       match_mem f m1 m1' ->
       Val.inject_list f vargs vargs' ->
       exists (f' : meminj) (vres' : val) (m2' : mem) (t' : trace),
         external_call ef ge2 vargs' m1' t' vres' m2' /\
         Val.inject f' vres vres' /\
         match_mem f' m2 m2' /\
         Mem.unchanged_on (loc_unmapped f) m1 m2 /\
         Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\
         inject_incr f f' /\
         inject_separated f f' m1 m1' /\ inject_trace f' t t'.

Definition Clight_self_simulation (p: program) :
    self_simulation (Clight.semantics2 p) _ memcore_to_state.
Proof. 
  eapply Build_self_simulation with (code_inject := code_inject); intros.
  { destruct c1; destruct c2; try contradiction; simpl in *. 
    + destruct H as [? [? [? [? ?]]]]. split; trivial. 
      split; trivial. 
      split. eapply cont_inject_incr; eauto.
      split. eapply env_inject_incr; eauto.
      eapply tenv_inject_incr; eauto. 
    + destruct H as [? [? ?]]. split; trivial. 
      split. apply mem_lemmas.forall_inject_val_list_inject in H1.
             exploit val_inject_list_incr; eauto.
             apply mem_lemmas.val_list_inject_forall_inject. 
      eapply cont_inject_incr; eauto.
  + destruct H. 
    split. eapply val_inject_incr; eauto. 
    eapply cont_inject_incr; eauto. }
{ assert (SI: symbols_inject f (Genv.to_senv g) (Genv.to_senv g)). admit. (*symbolsinject*)
  destruct H. simpl in *. remember (memcore_to_state c1 m1) as st. 
  remember (memcore_to_state c1' m1') as st'. remember (memcore_to_state c2 m2) as st2.
  assert (exists st2' f' t', step2 g st2 t' st2' /\
          let (c2',m2') := state_to_memcore st2' 
          in match_self code_inject f' c1' m1' c2' m2' /\
            is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) /\ inject_trace f' t t').
  Focus 2. { destruct H as [st2' [f' [t' [STEP2 X]]]].
             remember (state_to_memcore st2') as q; symmetry in Heqq; destruct q as [c2' m2'].
             destruct X as [MC X].
             exists c2', f', t', m2'. rewrite <- (memcore_to_state_correct _ _ _ Heqq). auto. }
  Unfocus.
  destruct matchmem.  
  generalize dependent m2. generalize dependent m1'. generalize dependent m1.
  generalize dependent c2. generalize dependent c1'. generalize dependent c1.
  induction H0; simpl; intros; destruct c1; simpl in Heqst; inv Heqst; destruct c1'; simpl in Heqst'; inv Heqst'; destruct c2; simpl in *; try contradiction.
  + destruct cinject as [? [? [? [? ?]]]]; subst. inv H4.
    exploit eval_lvalue_inject; try eassumption. reflexivity. 
    intros [b' [i' [EV_LV' Vinj]]].
    exploit eval_expr_inject; try eassumption. reflexivity. 
    intros [v2' [EV_EX' Vinj_V2]].
    exploit Cop.sem_cast_inject; try eassumption.
    intros [v' [CAST' Inj_v]]. rename loc into b. rename ofs into i.
    exploit assign_loc_inject_match_mem. eassumption. eassumption. eassumption.
      split. apply minject. eassumption. eassumption.
    intros [m2' [AL' [MINJ' LD']]]. 
    eexists; exists f, E0; split. 
    - econstructor; eassumption. 
    - simpl; split.
      * split; trivial. split; trivial. split. reflexivity. auto.
      * split; [| constructor]. red; intros. congruence.
  + destruct cinject as [? [SS [? [? ?]]]]; subst; inv SS.
      exploit eval_expr_inject; try eassumption. reflexivity.
      intros [v' [EV_EX' Vinj]]. unfold memcore_to_state; simpl. 
      eexists; exists f, E0; split.
      * econstructor. eassumption.
      * simpl. split.
        ++ constructor; trivial.  
           red; intuition. red; intros. rewrite 2 PTree.gsspec.
           destruct (peq x id); subst. trivial. apply H3.
           split; trivial.
        ++ split; [| constructor]. red; intros; congruence.
  + destruct cinject as [? [SS [? [? ?]]]]; subst; inv SS.
      exploit eval_expr_inject; try eassumption. reflexivity. 
      intros [vf' [EV_EX' VFinj]].
      exploit eval_exprlist_inject; try eassumption. apply exprlist_inject_refl.
      intros [vargs' [EV_ARGS' ArgsInj]].
      eexists; exists f, E0; split.
      * econstructor; eauto. red in SI.  admit. (*globenv*) 
      * simpl; split.
        ++ constructor; trivial.   
           red; intuition. destruct optid; simpl; repeat split; trivial.
           split; trivial.
        ++ split; [| constructor]. red; intros; congruence. 
  + (*Sbuiltin*)
      destruct cinject as [? [SS [? [? ?]]]]; subst. inv SS.
      exploit eval_exprlist_inject; try eassumption. apply exprlist_inject_refl. 
      intros [vargs' [EV_ARGS' ArgsInj]].

      (*exploit external_call_mem_inject_gen'; eauto. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.*)
      exploit external_call_match_mem_inject; eauto. split; eauto. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.
      intros [f' [vres' [m2' [t' [EC' [ResInj [MInj' [Unch1 [UNCH2 [INC [SEP ITRACE]]]]]]]]]]].
      eexists; exists f', t'; split.
      * econstructor; eassumption.
      * simpl; split.
        ++ constructor; trivial.   
           red; intuition.
           eapply cont_inject_incr; eassumption.
           eapply env_inject_incr; eassumption.
           destruct optid.
           +++ red; intros. simpl.  rewrite 2 PTree.gsspec.
             destruct (peq x i); subst. trivial.
             specialize (H4 x). destruct (t0 ! x); destruct (t1 ! x); try contradiction; trivial.
             -- eapply val_inject_incr; eauto.
           +++ eapply  tenv_inject_incr; eassumption.
        ++ split; trivial. red; intros.
           split. admit. (*ofs=0 in  externalcall??*)
           eapply SEP; eauto. 
  + destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    eexists; exists f, E0; split.
    - apply step_seq.
    - simpl; split.
      * constructor; trivial.   
           red; intuition. split; trivial. reflexivity. 
           split; trivial.
      * split; [| constructor]. simpl; red; intros; congruence. 
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS. 
    destruct c0; simpl in H; try contradiction. destruct H. 
    eexists; exists f; eexists; split.
    econstructor.
    simpl; split.
    * constructor; trivial.   
      red; intuition.
      split; trivial.
    * split. red; intros. congruence. 
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. destruct H.
    eexists; exists f; eexists; split.
    econstructor.
    simpl; split.
    * constructor; trivial.   
      red; intuition.
      split; trivial.
    * split. red; intros. congruence. 
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. destruct H.
    eexists; exists f; eexists; split.
    econstructor.
    simpl; split.
    * constructor; trivial.   
      red; intuition.
      split; trivial.
    * split. red; intros. congruence.   
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    exploit eval_expr_inject; try eassumption. reflexivity. 
    intros [v1' [EV_EX' V1inj]].
    exploit bool_val_inject; eauto. intros.
    eexists; exists f; eexists; split.
    econstructor; eauto.
    simpl; split.
    * constructor; trivial.   
      red; intuition.
      split; trivial.
    * split. destruct b; trivial.
        red; intros. congruence.
        red; intros. congruence.
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    eexists; exists f; eexists; split.
    econstructor. 
    simpl; split.
    * constructor; trivial.
      red; intuition. simpl. repeat split; trivial.
      split; trivial.
    * split. red; intros. congruence. 
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. 
    destruct c; try contradiction. destruct H0 as [? [? ?]]. inv SS. 
    eexists; exists f; eexists; split.
    eapply step_skip_or_continue_loop1; trivial. 
    simpl; split.
    * constructor; trivial.
      red; intuition. repeat split; trivial. repeat split; trivial.
      split; trivial.
    * split. red; intros. congruence. 
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. destruct H as [? [? ?]]. 
    eexists; exists f; eexists; split.
    eapply step_break_loop1. 
    simpl; split.
    * constructor; trivial.
      red; intuition.
      split; trivial.
    * split. red; intros. congruence.   
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. destruct H as [? [? ?]]. inv H; inv H2.
    eexists; exists f; eexists; split.
    eapply step_skip_loop2.
    simpl; split.
    * constructor; trivial.
      red; intuition. 
      split; trivial.
    * split. red; intros. congruence. 
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. destruct H as [? [? ?]]. inv H; inv H2. 
    eexists; exists f; eexists; split.
    eapply step_break_loop2.
    simpl; split.
    * constructor; trivial.
      red; intuition.
      split; trivial.
    * split. red; intros. congruence. 
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    exploit freelist_inject; eauto. eapply env_blocks_inject; eassumption. 
    intros [m2' [FL' INJ]].
    eexists; exists f; eexists; split.
    eapply step_return_0. eassumption.
    simpl; split.
    * constructor; trivial. split. constructor. eapply call_cont_inject; eauto. eapply match_mem_freelist; eauto.
      split; trivial. 
    * split; [| constructor]. red; intros; congruence. 
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    rename v0 into u.
    exploit eval_expr_inject; try eassumption. reflexivity.
    intros [v' [EV_EX' Vinj]].
    exploit Cop.sem_cast_inject; try eassumption. 
    intros [u' [CAST' Inj_u]].
    exploit freelist_inject; eauto. eapply env_blocks_inject; eassumption. 
    intros [m2' [FL' INJ]].
    eexists; exists f; eexists; split.
    eapply step_return_1; eassumption.
    simpl; split.
    * split; trivial. split; trivial. eapply call_cont_inject; eauto. eapply match_mem_freelist; eauto. 
      split; trivial. 
    * split; [| constructor]. red; intros; congruence. 
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    exploit freelist_inject; eauto. eapply env_blocks_inject; eassumption. 
    intros [m2' [FL' INJ]].
    eexists; exists f; eexists; split. 
    eapply (is_call_cont_inject _ _ _ H1) in H.
    eapply step_skip_call; eauto.
    simpl. split. split; trivial. split; trivial. eapply match_mem_freelist; eauto. 
      split; trivial. 
    split; [| constructor]. red; intros; congruence. 
  + destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    exploit eval_expr_inject; try eassumption. reflexivity. 
    intros [v' [EV_EX' Vinj]].
    exploit sem_switch_arg_inject; eauto.
    eexists; exists f; eexists; split.
    eapply step_switch; eauto. 
    simpl; split.
    * split. red; simpl; intuition. split; trivial. 
    * split. red; intros; congruence.
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. 
    eexists; exists f; eexists; split.
      eapply step_skip_break_switch; trivial.
    simpl; split.
    * split. split; intuition. split; trivial.
    * split. red; intros; congruence.
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    destruct c0; try contradiction. 
    eexists; exists f; eexists; split.
    apply step_continue_switch. 
    simpl; split.
    * split. split; intuition. split; trivial.
    * split. red; intros; congruence.
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    eexists; exists f; eexists; split.
    apply step_label.
    simpl; split. 
    * split. split; intuition. split; trivial.
    * split. red; intros; congruence.
      constructor.
  + simpl. destruct cinject as [X [SS [? [? ?]]]]; subst. inv SS.
    exploit find_label_inject. apply call_cont_inject. eassumption. 
    instantiate (2:=lbl). instantiate (1:=fn_body f1). rewrite H.
    intros [kk1 [FL CI]].
    eexists; exists f; eexists; split.
    eapply step_goto; eauto. 
    simpl; split.
    * split. split; intuition. split; trivial.
    * split. red; intros; congruence.
      constructor.
  + simpl. destruct cinject as [? [? ?]]; subst.
    exploit function_entry2_inject_match_mem; eauto. split; eauto. 
    intros [j' [e' [te' [m2' [FE' [EI [TI [MI [INC SEP]]]]]]]]].
    eexists; exists j'; eexists; split. 
    eapply step_internal_function. eassumption.
    simpl; split.
    * split; trivial. split; intuition.
      eapply cont_inject_incr; eauto. 
    * split; trivial. 
      constructor. 
  + destruct cinject as [? [? ?]]; subst.
      (*exploit external_call_mem_inject_gen'; eauto. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.*)
      exploit external_call_match_mem_inject; eauto. split; eauto. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.
      intros [f' [vres' [m2' [t' [EC' [ResInj [MInj' [Unch1 [UNCH2 [INC [SEP ITRACE]]]]]]]]]]].
      eexists; exists f', t'; split. 
      eapply step_external_function. eauto. 
      simpl; split.
      * split. split; intuition. eapply cont_inject_incr; eauto.
        trivial.
      * split. red; intros. destruct (SEP _ _ _ H3 H0). split. admit. (*d=0 in externalcall*) split; eauto.
        trivial.
  + simpl. destruct cinject as [X SS]; subst.
    destruct c0; try contradiction. destruct SS as [? [? [? [? ?]]]]; subst.
    destruct optid; destruct o; try contradiction; subst.
    { eexists; exists f, E0; split. 
      eapply step_returnstate.  
      simpl; split.
      * split. split; intuition.
          red; intros. rewrite 2 PTree.gsspec.
          destruct (peq x i0); subst. trivial. apply H2.
        split; trivial.
      * split. red; intros; congruence.
        constructor. }
    { eexists; exists f, E0; split. 
      eapply step_returnstate.  
      simpl; split.
      * split. split; intuition. split; trivial.
      * split. red; intros; congruence.
        constructor.
Admitted.
    
    
