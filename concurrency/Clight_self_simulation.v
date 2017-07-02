Require Import Coqlib.
Require Import Values.
Require Import Integers.
Require Import Maps.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Cop.
Require Import Clight.

Require Import concurrency.self_simulation.

Set Bullet Behavior "Strict Subproofs".

Lemma is_ext_seperated j j' m m' (E:is_ext j (Mem.nextblock m) j' (Mem.nextblock m')):
  inject_separated j j' m m'.
Proof. 
  red; intros. destruct (E _ _ _ H0 H) as [? [? ?]]; split; trivial.
Qed.
(*
Lemma match_mem_inj j m m' (M:match_mem j m m')
      j' (INC: inject_incr j j') (SEP:  inject_separated j j' m m'): j'=j.
Proof.
  apply compcert.lib.Axioms.extensionality; intros b.
remember (j b) as q; symmetry in Heqq; destruct q.
+ destruct p. apply INC; trivial.
+ remember (j' b) as w; symmetry in Heqw; destruct w; trivial.
  destruct p. destruct (SEP _ _ _ Heqq Heqw); exfalso.
  (*
Lemma match_mem_inj j m m' (M:match_mem j m m')
      j' (J: is_ext j (Mem.nextblock m) j' (Mem.nextblock m'))
      (I: inject_incr j j'):
      j'=j.
Proof.
  red in J.
*)

Lemma match_mem_inject_incr m m' j j' (I:inject_incr j j') (SEP: inject_separated j j' m m')
      (M: match_mem j m m'): match_mem j' m m'.
Proof.
  destruct M. constructor.
+ split; intros.
  - split; intros.
    * eapply minject; eauto.  
      remember (j b1) as q; symmetry in Heqq; destruct q.
      ++ destruct p0. rewrite (I _ _ _ Heqq) in H; trivial.
      ++ apply Mem.perm_valid_block in H0. destruct (SEP _ _ _ Heqq H); contradiction.
    * eapply minject; eauto. instantiate (1:=b2).  
      remember (j b1) as q; symmetry in Heqq; destruct q.
      ++ destruct p0. rewrite (I _ _ _ Heqq) in H; trivial.
      ++ specialize (size_chunk_pos chunk); intros. destruct (SEP _ _ _ Heqq H).
         elim H2; clear H2 H3. eapply Mem.perm_valid_block.
         apply (H0 ofs). omega. 
    * remember (j b1) as q; symmetry in Heqq; destruct q.
      ++ destruct p. rewrite (I _ _ _ Heqq) in H; inv H. 
         eapply memval_inject_incr; eauto. apply minject; eauto. 
      ++ apply Mem.perm_valid_block in H0. destruct (SEP _ _ _ Heqq H); contradiction. 
  - assert (X: j b = None) by (eapply minject; trivial).
    remember  (j' b) as q; symmetry in Heqq; destruct q; trivial. destruct p.
    destruct (SEP _ _ _ X Heqq). red in ppreimage. red in pimage. red in pinject. admit.   
  - admit.
  - red; intros. 
    remember (j b1) as q; symmetry in Heqq; destruct q.
    * destruct p. rewrite(I _ _ _ Heqq) in H0; inv H0.
      remember (j b2) as w; symmetry in Heqw; destruct w.
      ++ destruct p. rewrite (I _ _ _ Heqw) in H1; inv H1.
         eapply minject; eassumption.
      ++ apply Mem.perm_valid_block in H3. destruct (SEP _ _ _ Heqw H1); contradiction.
    * apply Mem.perm_valid_block in H2. destruct (SEP _ _ _ Heqq H0); contradiction. 
  - remember (j b) as q; symmetry in Heqq; destruct q.
    * destruct p. rewrite(I _ _ _ Heqq) in H; inv H. eapply minject; eassumption.
    * destruct H0 as [HH |HH]; apply Mem.perm_valid_block in HH; 
      destruct (SEP _ _ _ Heqq H); contradiction. 
  - remember (j b1) as q; symmetry in Heqq; destruct q.
    * destruct p0. rewrite(I _ _ _ Heqq) in H; inv H. eapply minject; eassumption.
    * apply Mem.perm_valid_block in H0.
      destruct (SEP _ _ _ Heqq H); contradiction. 
+ red; intros. split; intros. 
  - destruct (pimage b1 ofs) as [? [? ?]]. eapply Mem.perm_implies; eauto. destruct p; constructor.
    rewrite (I _ _ _ H1) in H. inv H.
    eapply pinject; eauto.
  - destruct (ppreimage b2 (ofs+delta)) as [b [bb [d [? [? ?]]]]].
       eapply Mem.perm_implies; eauto. destruct p; constructor.
    destruct (eq_block b1 b); subst.
    * rewrite (I _ _ _ H1) in H; inv H. assert (ofs=d) by omega. subst.
      inv minject. destruct (mi_perm_inv _ _ _ _ _ _ H1 H0). trivial.
      elim H; clear - H2. eapply Mem.perm_max; eauto. 
    * remember (j b1) as q; symmetry in Heqq; destruct q.
      ++ destruct p0. rewrite (I _ _ _ Heqq) in H; inv H. eapply pinject; eauto.
      ++ destruct (SEP _ _ _ Heqq H). apply Mem.perm_valid_block in H0. contradiction. 
+ red; intros. apply pimage in H. destruct H as [? [? ?]]. rewrite (I _ _ _ H).
  eexists; eexists; reflexivity.
+ red; intros. destruct (ppreimage _ _ H) as [bb [d [ofs [J [Perm X]]]]].
  apply I in J. exists bb, d, ofs; auto.
Qed. 
*)
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
(*
Lemma unary_op_inject j f: forall v t m u (UNOP: Cop.sem_unary_operation f v t m = Some u)
      m' (M: Mem.inject j m m') v' (V: Val.inject j v v'), 
  exists u', Cop.sem_unary_operation f v' t m' = Some u' /\ Val.inject j u u'.
Proof.
destruct f; intros; simpl in *.
+ unfold Cop.sem_notbool in *. destruct (Cop.classify_bool t); try discriminate.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. unfold Val.of_bool. destruct (Integers.Int.eq i Integers.Int.zero); constructor.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. unfold Val.of_bool. destruct (Floats.Float.cmp Integers.Ceq f Floats.Float.zero); constructor.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. unfold Val.of_bool. destruct (Floats.Float32.cmp Integers.Ceq f Floats.Float32.zero); constructor.
  - destruct v; try contradiction; try discriminate.
    * inv UNOP. inv V.
      eexists; split. reflexivity. unfold Val.of_bool. destruct (Integers.Int.eq i Integers.Int.zero); constructor.
    * remember (Mem.weak_valid_pointer m b (Integers.Int.unsigned i)) as p; destruct p; try discriminate.
      inv UNOP. inv V.
      erewrite Mem.weak_valid_pointer_inject_val; eauto.
      eexists; split. reflexivity. constructor.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. unfold Val.of_bool. destruct (Integers.Int64.eq i Integers.Int64.zero); constructor.
+ unfold Cop.sem_notint in *. destruct (Cop.classify_notint t); try discriminate.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor. 
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor.
+ unfold Cop.sem_neg in *. destruct (Cop.classify_neg t); try discriminate.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor. 
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor. 
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor.
+ unfold Cop.sem_absfloat in *. destruct (Cop.classify_neg t); try discriminate.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor. 
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor.
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor. 
  - destruct v; try contradiction; try discriminate. inv UNOP. inv V.
    eexists; split. reflexivity. constructor.
Qed.
*)
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
+ destruct (H0 j _ _ _ _ H2 H3 H4 H5) as [b' [i' [EV VIN]]]; inv H2.
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
  -  (*apply H5 in H0. econstructor; eauto.  *) admit.
+ destruct a'; try contradiction; inv H1.
  assert (A: expr_inject a' a'). red; trivial.
(*  destruct H1 as [? ?]; subst; simpl.*)
  destruct (H0 _ _ _ _ _ A H2 H3 H4) as [v' [EVAL V]]. inv V.
  exists b2; eexists; split; econstructor; eauto.
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
Admitted.

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
  set (R := fun (x: (block * Ctypes.type)) (y: (block * Ctypes.type)) =>
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
Admitted. 

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
+ exploit Mem.alloc_parallel_inject; eauto. instantiate (1:=0); omega. instantiate (1:=Ctypes.sizeof ty); apply Z.le_refl.
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

Lemma alloc_variables_inject_match_mem g: forall vars j e m e1 m1 (A:alloc_variables g e m vars e1 m1)
      e' (E:env_inject j e e') m' (M: match_mem j m m'),
      exists j' e1' m1', alloc_variables g e' m' vars e1' m1' /\ env_inject j' e1 e1' /\ 
                         match_mem j' m1 m1' /\ inject_incr j j' /\ inject_separated j j' m m'.
Proof.
induction vars; simpl; intros; inv A.
+ exists j, e', m'; split. constructor. split; trivial. split; trivial.
  split. apply inject_incr_refl. red; intros; congruence. 
+ destruct M. exploit Mem.alloc_parallel_inject; eauto. instantiate (1:=0); omega. instantiate (1:=Ctypes.sizeof ty); apply Z.le_refl.
  intros [j' [m2' [b1' [ALLOC' [MINJ [INC [HJ' SEP]]]]]]].
  exploit (IHvars j' _ _ _ _ H6). 
  - instantiate (1:=(PTree.set id (b1', ty) e')).
    red; intros. rewrite 2 PTree.gsspec.
    destruct (peq x id); subst. split; trivial. eapply env_inject_incr; eassumption.
  - split.
    * eassumption.
    * red; intros. specialize (SEP b0).
      destruct (eq_block b0 b1); subst.
      ++ clear SEP; rewrite H in HJ'; inv HJ'. 
         split; intros.
         -- apply (Mem.perm_alloc_inv _ _ _ _ _ H3) in H0.
            destruct (eq_block b1 b1).
            ** eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto. omega. constructor.
            ** elim n; trivial. 
         -- apply (Mem.perm_alloc_inv _ _ _ _ _ ALLOC') in H0.
            destruct (eq_block b1' b1').
            ** eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto. omega. constructor.
            ** elim n; trivial.
     ++ rewrite (SEP n) in *. red in pinject. destruct (pinject _ _ _ H ofs p). 
        split; intros. 
        -- eapply MINJ; eauto.
        -- eapply Mem.perm_alloc_1. eassumption. apply H1. eapply Mem.perm_alloc_4. eassumption. eassumption.
           intros N; subst. exploit Mem.valid_block_inject_2. apply H. apply minject. intros V.
           apply Mem.fresh_block_alloc in ALLOC'. contradiction.
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

Lemma function_entry2_inject_match_mem g f j args m e te m1 (FE: function_entry2 g f args m e te m1)
      args' (ARGS: Forall2 (Val.inject j) args args') m' (M: match_mem j m m'):
      exists j' e' te' m1', function_entry2 g f args' m' e' te' m1' /\ 
                            env_inject j' e e' /\ tenv_inject j' te te' /\ match_mem j' m1 m1' /\
                            inject_incr j j' /\ inject_separated j j' m m'.
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
Qed.

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
+ eapply perm_inject_freelist. eassumption. apply minject. eassumption. eassumption. eassumption. eassumption.
+ red; intros. exploit perm_freelist_A. 2: eassumption. eassumption. intros [P B].
  eapply pimage; eauto.
+ eapply perm_preimage_freelist; eauto.
Qed.

Definition Clight_self_simulation (p: program) :
    self_simulation (Clight.semantics2 p) Clight.get_mem.
Proof. 
eapply Build_self_simulation with (code_inject := code_inject); intros.
{ constructor.
  + destruct s1; destruct s2; inv H; simpl; apply H1.
  + destruct s1; destruct s2; inv H; simpl; apply H1.
  + destruct s1; destruct s2; inv H; simpl; apply H1.
  + destruct s1; destruct s2; inv H; simpl; apply H1. }
admit. (*
{ destruct c1; destruct c2; inv H; simpl.
  + destruct H3 as [? [? [? [? INJ]]]].  
    split; [trivial | split]. trivial. (* eapply stmt_inject_incr; eauto.*)
    split. eapply cont_inject_incr; eauto.
    split. eapply env_inject_incr; eauto.
    split. eapply tenv_inject_incr; eauto.
    simpl in H1. red in H1; simpl in H1.
    eapply match_mem_inject_incr; eauto.
  + destruct H3 as [? [? ?]]. split; trivial.
    split.
      apply mem_lemmas.forall_inject_val_list_inject in H.
      exploit val_inject_list_incr; eauto.
      apply mem_lemmas.val_list_inject_forall_inject. 
    split. eapply cont_inject_incr; eauto.
    eapply match_mem_inject_incr; eauto.
  + destruct H3; split. eapply val_inject_incr; eauto.
    split. eapply cont_inject_incr; eauto.
    eapply match_mem_inject_incr; eauto. }*)
{ assert (SI: symbols_inject f (Genv.to_senv g) (Genv.to_senv g)). admit.

 induction H0; destruct c2; simpl in H; try contradiction.
  + destruct H as [? [? [? [? [? ?]]]]]. destruct s; inv H4.
    exploit eval_lvalue_inject; try eassumption. red; reflexivity. apply H8.      
    intros [b' [i' [EV_LV' Vinj]]].
    exploit eval_expr_inject; try eassumption. reflexivity. apply H8. 
    intros [v2' [EV_EX' Vinj_V2]].
    exploit Cop.sem_cast_inject; try eassumption. apply H8.
    intros [v' [CAST' Inj_v]].
    (*rewrite (expr_inject_type_of _ _ _ H7) in CAST'; eauto.
    rewrite (expr_inject_type_of _ _ _ H) in CAST'; eauto.*)
    admit. (*exploit assign_loc_inject; eauto. apply H8.
    intros [m1' [AL' MINJ']].
    rewrite (expr_inject_type_of _ _ _ H) in AL'; eauto.
    eexists; exists f, E0; split. 
    - econstructor. eassumption. eassumption. eassumption. eassumption.
    - simpl. split.
      * split; trivial. split; trivial. split; trivial. split; trivial.
        split; trivial. admit. (*match_mem*)
      * split; [| constructor]. red; intros. congruence.*)
  + destruct H as [? [SS [? [? [? ?]]]]]; subst. destruct s; try contradiction; inv SS. 
    (*- rename e1 into a'. rename k0 into k'. rename e0 into e'. rename le0 into le'. rename m0 into m'.*)
      exploit eval_expr_inject; try eassumption. reflexivity. apply H4. 
      intros [v' [EV_EX' Vinj]].
      eexists; exists f, E0; split.
      * econstructor. eassumption.
      * simpl; split.
        ++ intuition.
           red; intros. rewrite 2 PTree.gsspec.
           destruct (peq x i); subst. trivial. apply H3.
        ++ split; [| constructor]. red; intros; congruence.
  + destruct H as [? [SS [? [? [? ?]]]]]; subst. destruct s; try contradiction; inv SS. 
    (*destruct optid.
    - destruct o. destruct SS as [? [? ?]]; try contradiction; subst.
      rename e1 into a'. rename k0 into k'. rename e0 into e'. rename le0 into le'.
      rename m0 into m'. rename l into al'.*)
      exploit eval_expr_inject; try eassumption. reflexivity. apply H8.
      intros [vf' [EV_EX' VFinj]].
      exploit eval_exprlist_inject; try eassumption. apply H8. instantiate (1:=l). apply exprlist_inject_refl.
      intros [vargs' [EV_ARGS' ArgsInj]].
      eexists; exists f, E0; split.
      * econstructor; eauto. admit. (*globenv*) 
      * simpl; split.
        ++ intuition. destruct o; trivial.
        ++ split; [| constructor]. red; intros; congruence. (*
    - destruct o; destruct SS as [? [? ?]]; try contradiction; subst.
      rename e1 into a'. rename k into k'. rename e0 into e'. rename le0 into le'.
      rename m0 into m'. rename l into al'.
      exploit eval_expr_inject; try eassumption. apply H8. 
      intros [vf' [EV_EX' VFinj]].
      exploit eval_exprlist_inject; try eassumption. apply H8. 
      intros [vargs' [EV_ARGS' ArgsInj]].
      eexists; exists f, E0; split.
      * econstructor.
        rewrite <- (expr_inject_type_of _ _ _ H9); eauto. eassumption. eassumption.
        instantiate (1:=fd). admit. (*globenv*) assumption.
      * simpl; split.
        ++ intuition.
        ++ split; [| constructor]. red; intros; congruence.*)
  + destruct H as [? [SS [? [? [? ?]]]]]; subst. inv SS.
    (*destruct s; try contradiction. 
    destruct optid.
    - destruct o; destruct SS as [? [? [? ?]]]; try contradiction; subst.
      rename k0 into k'. rename e0 into e'. rename le0 into le'.
      rename m0 into mm'. rename l into al'.*)
      exploit eval_exprlist_inject; try eassumption. apply H5. instantiate (1:=al). apply exprlist_inject_refl. 
      intros [vargs' [EV_ARGS' ArgsInj]].
      exploit external_call_mem_inject_gen'; eauto. apply H5. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.
      intros [f' [vres' [m2' [t' [EC' [ResInj [MInj' [Unch1 [UNCH2 [INC [SEP ITRACE]]]]]]]]]]].
      eexists; exists f', t'; split.
      * econstructor; eassumption.
      * simpl; split.
        ++ intuition.
           eapply cont_inject_incr; eassumption.
           eapply env_inject_incr; eassumption.
           destruct optid.
           +++ red; intros. simpl.  rewrite 2 PTree.gsspec.
             destruct (peq x i); subst. trivial.
             specialize (H4 x). destruct (le ! x); destruct (le0 ! x); try contradiction; trivial.
             -- eapply val_inject_incr; eauto.
           +++ eapply  tenv_inject_incr; eassumption.
           +++ rename m0 into m2. admit. (*match_mem externalcall*)
        ++ split; trivial. red; intros.
           split. admit. (*ofs=0??*)
           eapply SEP; eauto. (* 
    - destruct o; destruct SS as [? [? [? ?]]]; try contradiction; subst.
      rename k0 into k'. rename e0 into e'. rename le0 into le'.
      rename m0 into mm'. rename l into al'.
      exploit eval_exprlist_inject; try eassumption. apply H5. 
      intros [vargs' [EV_ARGS' ArgsInj]].
      exploit external_call_mem_inject_gen'; eauto. apply H5. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.
      intros [f' [vres' [m2' [t' [EC' [ResInj [MInj' [Unch1 [UNCH2 [INC [SEP ITRACE]]]]]]]]]]].
      eexists; exists f', t'; split.
      * econstructor; eassumption.
      * simpl; split.
        ++ intuition.
           eapply cont_inject_incr; eassumption.
           eapply env_inject_incr; eassumption.
           eapply tenv_inject_incr; eassumption.
           admit. (*match_mem*)
        ++ split; trivial. red; intros.
           split. admit. (*ofs=0??*)
           eapply SEP; eauto. *)
  + destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
(*    destruct s; try contradiction. destruct H.*)
    eexists; exists f, E0; split.
    - apply step_seq.
    - split. simpl. intuition.
      split; [| constructor]. simpl; red; intros; congruence. 
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    (*destruct s0; try contradiction.*) destruct k0; try contradiction. destruct H0.
    eexists; exists f; eexists; split.
    econstructor.
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    destruct k0; try contradiction. destruct H0.
    eexists; exists f; eexists; split.
    econstructor.
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    destruct k0; try contradiction. destruct H0.
    eexists; exists f; eexists; split.
    econstructor.
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    exploit eval_expr_inject; try eassumption. reflexivity. apply H5. 
    intros [v1' [EV_EX' V1inj]].
    exploit bool_val_inject; eauto. apply H5. intros.
    eexists; exists f; eexists; split.
    econstructor; eauto. (* eassumption.
      rewrite <- (expr_inject_type_of _ _ _ H); eauto.*)
    simpl. intuition.
    destruct b; trivial.
    red; intros. congruence.
    red; intros. congruence.
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    eexists; exists f; eexists; split.
    econstructor. 
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H. 
    destruct k0; try contradiction. destruct H1 as [? [? ?]]. inv H. inv H1. 
    eexists; exists f; eexists; split.
    eapply step_skip_or_continue_loop1; trivial. 
    simpl. intuition.
    red; intros. congruence. 
    constructor.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    destruct k0; try contradiction. destruct H0 as [? [? ?]]. inv H. inv H0. 
    eexists; exists f; eexists; split.
    eapply step_break_loop1. 
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    destruct k0; try contradiction. destruct H0 as [? [? ?]]. inv H; inv H0. 
    eexists; exists f; eexists; split.
    eapply step_skip_loop2.
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    destruct k0; try contradiction. destruct H0 as [? [? ?]]. inv H; inv H0. 
    eexists; exists f; eexists; split.
    eapply step_break_loop2.
    simpl. intuition.
    red; intros. congruence. 
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    (*destruct s; try contradiction. destruct o; try contradiction. *)
    exploit freelist_inject; eauto. apply H4. eapply env_blocks_inject; eassumption. 
    intros [m1' [FL' INJ']].
    eexists; exists f; eexists; split.
    eapply step_return_0. eassumption.
    simpl. split. split. constructor. split. eapply call_cont_inject; eauto.
    - clear - H2 H0 FL' INJ' H4. eapply match_mem_freelist; eauto.
    - split; [| constructor]. red; intros; congruence.   
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    (*destruct s; try contradiction. destruct o; try contradiction.  *)
    rename v' into u.
    exploit eval_expr_inject; try eassumption. reflexivity. apply H6. 
    intros [v' [EV_EX' Vinj]].
    exploit Cop.sem_cast_inject; try eassumption. apply H6.
    intros [u' [CAST' Inj_u]].
    exploit freelist_inject; eauto. apply H6. eapply env_blocks_inject; eassumption. 
    intros [m1' [FL' INJ]].
 (*   rewrite (expr_inject_type_of _ _ _ H) in CAST'.*)
    eexists; exists f; eexists; split.
    eapply step_return_1; eassumption.
    simpl. split. split; trivial. split. eapply call_cont_inject; eauto. eapply match_mem_freelist; eauto.
    split; [| constructor]. red; intros; congruence. 
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    exploit freelist_inject; eauto. apply H5. eapply env_blocks_inject; eassumption. 
    intros [m1' [FL' INJ]].
    eexists; exists f; eexists; split. 
    eapply (is_call_cont_inject _ _ _ H2) in H0.
    eapply step_skip_call; eauto.
    simpl. split. split; trivial. split; trivial. eapply match_mem_freelist; eauto.
    split; [| constructor]. red; intros; congruence. 
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    exploit eval_expr_inject; try eassumption. reflexivity. apply H5. 
    intros [v' [EV_EX' Vinj]].
    exploit sem_switch_arg_inject; eauto.
    (*rewrite (expr_inject_type_of _ _ _ H); intros. *)
    eexists; exists f; eexists; split.
    eapply step_switch; eauto. 
    simpl. intuition. (* apply seq_of_lbldl_stmt_inject. simpl. admit. (*switch*)*)
    red; intros; congruence.
    constructor.
  + simpl. destruct H as [X [? [H [? [? ?]]]]]; subst. inv H1.
    destruct k0; try contradiction. (* destruct H0; subst. destruct s; try contradiction. *)
    - eexists; exists f; eexists; split.
      eapply step_skip_break_switch; trivial.
      simpl. intuition.
      red; intros; congruence.
      constructor.
      red; intros; congruence.
      constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    destruct k0; try contradiction. 
    eexists; exists f; eexists; split.
    apply step_continue_switch. 
    simpl. intuition.
    red; intros; congruence.
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    eexists; exists f; eexists; split.
    apply step_label.
    simpl. intuition.
    red; intros; congruence.
    constructor.
  + simpl. destruct H as [X [H [? [? [? ?]]]]]; subst. inv H.
    exploit find_label_inject. apply call_cont_inject. eassumption. 
    instantiate (2:=lbl). instantiate (1:=fn_body f1). rewrite H0.
    intros [kk1 [FL CI]].
    eexists; exists f; eexists; split.
    eapply step_goto; eauto. 
    simpl. intuition. 
    red; intros; congruence.
    constructor.
  + simpl. destruct H as [? [? [? ?]]]; subst.
    exploit function_entry2_inject_match_mem; eauto. 
    intros [j' [e' [te' [m1' [FE' [EI [TI [MI [INC SEP]]]]]]]]].
    eexists; exists j'; eexists; split. 
    eapply step_internal_function. eassumption.
    simpl. rename args into vargs'. rename f into j. rename f0 into f.
      rename m0 into m'. rename k0 into k'. intuition.
    - eapply cont_inject_incr; eauto.
    - red; intros. destruct (SEP _ _ _ H4 H). split. admit. (*ofs=0*) split; auto.
    - constructor. 
  + simpl. destruct H as [? [? [? ?]]]; subst.
      exploit external_call_mem_inject_gen'; eauto. apply H3. eapply mem_lemmas.forall_inject_val_list_inject; eassumption.
      intros [f' [vres' [m2' [t' [EC' [ResInj [MInj' [Unch1 [UNCH2 [INC [SEP ITRACE]]]]]]]]]]].
      eexists; exists f', t'; split. 
      eapply step_external_function. eauto. 
      simpl. intuition. eapply cont_inject_incr; eauto.
      admit. (*match_mem - externalcall*)
      red; intros. destruct (SEP _ _ _ H4 H). split. admit. (*d=0*) split; eauto.
  + simpl. destruct H as [X [H ?]]; subst.
    destruct k0; try contradiction. destruct H as [? [? [? [? ?]]]]; subst.
    destruct optid; destruct o; try contradiction; subst.
    - eexists; exists f, E0; split. 
      eapply step_returnstate.  
      simpl. intuition.
      * red; intros. rewrite 2 PTree.gsspec.
        destruct (peq x i0); subst. trivial.
        specialize (H3 x). destruct (le ! x); destruct (t ! x); try contradiction; trivial.
      * red; intros; congruence.
      * constructor.
    - eexists; exists f, E0; split. 
      eapply step_returnstate.  
      simpl. intuition.
      * red; intros; congruence.
      * constructor.
Admitted.
    
    