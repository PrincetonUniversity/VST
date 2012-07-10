Require Import msl.examples.cont.language.
Require Import msl.msl_standard.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import msl.Coqlib2.


(******  CONSTRUCTION OF rmap FOR THE CONT LANGUAGE *****)

Inductive kind := VAL: adr -> kind | FUN: list var -> kind.

Module AV0 <: ADR_VAL0.
 Definition address := adr.
 Definition some_address := 0.
 Definition kind := kind.
End AV0.

Module AV := SimpleAdrVal AV0.
Module R := Rmaps AV.
Module RML := Rmaps_Lemmas R.
Export RML. Export R.
Instance Cross_rmap : Cross_alg rmap := Cross_rmap_simple (fun _ => I).

Obligation Tactic := idtac.

(******  MAPSTO AND RELATED OPERATORS *****)

Program Definition mapsto (v1 v2: adr) : pred rmap :=
  fun w => forall i,
         if eq_dec i v1 then w @ i = YES pfullshare (VAL v2) NoneP else identity (w @ i).
Next Obligation.
 intros. intros ? ? ? ?.
  intro i; specialize (H0 i).
  destruct (eq_dec i v1).
  apply (age1_YES _ _ _ _ _ H); auto.
  destruct (identity_resource (a @ i)) as [? _]. specialize (H1 H0).
  apply identity_resource. 
  generalize (age1_resource_at _ _ H i (a @ i)); intro.
  generalize (resource_at_approx a i); intro. 
  destruct (a @ i); try contradiction.
  rewrite H2; simpl in *; auto.
  rewrite H2; simpl in *; auto.
Qed.

Lemma singleton_rmap_OK: 
   forall v v' m,  
       resource_fmap (approx (level m))
            oo (fun i => if eq_dec i v then YES pfullshare (VAL v') NoneP else core m @  i) =
    (fun i => if eq_dec i v then YES pfullshare (VAL v') NoneP else core m @ i).
Proof.
  intros; extensionality i; unfold compose; simpl.
  destruct (eq_dec i v). 
  unfold resource_fmap. f_equal. apply preds_fmap_NoneP.
  rewrite <- level_core.
  symmetry; apply resource_at_approx.
Qed.

Definition singleton_rmap  (v v': adr) (m: rmap) : rmap :=
  proj1_sig 
  (make_rmap (fun i => if eq_dec i v then YES pfullshare (VAL v') NoneP  else core m @ i ) 
    I (level m) (singleton_rmap_OK _ _ m)).

Lemma singleton_rmap_level: forall x y m,
      level (singleton_rmap x y m) = level m.
Proof. 
  intros.  apply level_make_rmap.
Qed.

Lemma singleton_rmap_mapsto:
   forall x y n, app_pred (mapsto x y) (singleton_rmap x y n).
 Proof.
  intros. hnf. simpl snd.
  unfold singleton_rmap.
  intro; repeat rewrite resource_at_make_rmap.
  change AV.address with adr.
 destruct (eq_dec i x); auto.
 apply resource_at_core_identity.
Qed.

Local Open Scope pred.

Lemma mapsto_uniq: forall (x y: adr) w w', core w = core w' -> mapsto x y w -> mapsto x y w' -> w=w'.
Proof.
  intros.
 apply rmap_ext.
 assert (level (core w) = level (core w')) by congruence.
 do 2 rewrite level_core in H2. auto.
 intro. 
 specialize (H0 l); specialize (H1 l).
 destruct (@eq_dec adr _ l x); try congruence.
 apply identity_unit_equiv in H0.
 apply unit_core in H0.
 apply identity_unit_equiv in H1.
 apply unit_core in H1.
 rewrite core_resource_at in *. congruence.
Qed.

Lemma mapsto_e1: forall v1 v2 w,
       app_pred (mapsto v1 v2 * TT) w ->
       w @ v1 = YES pfullshare (VAL v2) NoneP.
Proof.
 intros.
 destruct H as [w1 [w2 [? [? ?]]]].
 hnf in H0.
 specialize (H0 v1).
 apply (resource_at_join _ _ _ v1) in H.
 rewrite if_true in H0 by auto. rewrite H0 in H.
apply join_YES_pfullshare1 in H. inv H; auto.
Qed.

(* LOCAL VARIABLE ENVIRONMENTS *)

Definition env := var -> adr.

Definition env_set (f: env) (x: var) (y: adr) :=
   fun i => if eq_dec i x then y else f i.

Lemma env_gss : forall s x y, env_set s x y x = y.
Proof. unfold env_set; intros.  rewrite if_true; auto. 
Qed.
Lemma env_gso: forall s x y z, x<>z -> env_set s x y z = s z.
Proof. unfold env_set; intros; rewrite if_false; auto. 
Qed.

Definition locals2env (s: locals) : env := 
   fun x => match table_get s x with Some a => a | None => 0 end.

Fixpoint eval (e: expr) : env -> adr :=
 fun s =>
 match e with
 | Const n => n
 | Var x => s x
 | Offset e n => n + eval e s
 | Mem e => 0
 end.

Definition eval_list (xs: list expr) : env -> (list adr) := fun s => map (fun e => eval e s) xs.

Lemma offset_zero:  forall a, eval (a .+ 0) = eval a.
Proof. intros. extensionality s; simpl; destruct (eval a s); simpl; f_equal; auto.
Qed.

Lemma offset_offset: forall a n m, 
  eval ((a .+ n) .+ m) = eval (a .+ (n+m)).
Proof.
 intros.
 extensionality s. simpl. 
 destruct (eval a s); simpl; unfold adr; omega. 
Qed.

Definition assert := env -> pred rmap.
Bind Scope pred with assert.

Definition subst (x: var) (v: adr) (P: assert) : assert :=
   fun s => P (env_set s x v).

Definition arguments (vars: list var) (vl: list adr) : env :=
      locals2env (mk_locals vars vl).
Opaque arguments.

Lemma locals2env_table_set: 
  forall x y s, locals2env (table_set x y s) = env_set (locals2env s) x y.
Proof. intros; extensionality i. unfold locals2env, env_set, table_set.
  simpl. destruct (eq_dec i x); auto.
Qed.

(* TYPE-CHECKING OF LOCAL VARIABLES *)

Require ListSet.
Definition varset : Type := ListSet.set var.
Definition vs_mem: var -> varset -> bool := ListSet.set_mem EqDec_var.
Definition vs_add: var -> varset -> varset := ListSet.set_add EqDec_var.

Definition varcompat (vars: varset) (s: locals) :=
   forall i, vs_mem i vars = true -> table_get s i <> None.

Fixpoint expcheck (vars: varset) (e: expr) :=
  match e with
  | Const _ => true
  | Var v => vs_mem v vars
  | Offset e n => expcheck vars e
  | Mem _ => false
  end.

Fixpoint typecheck (vars: varset) (c: control) : bool :=
 match c with 
  | Assign (Var v) (Mem e) c' => andb (expcheck vars e)
                                         (typecheck (vs_add v vars) c')
  | Assign (Var v) e c' => andb (expcheck vars e)
                                         (typecheck (vs_add v vars) c')
  | Assign (Mem e1) e2 c' => andb (andb (expcheck vars e1)  (expcheck vars e2))
                                         (typecheck vars c')
  | language.If e c1 c2 => andb (expcheck vars e) 
                                            (andb (typecheck vars c1) (typecheck vars c2))
  | Go e el => andb (expcheck vars e)  (forallb (expcheck vars) el)
  | _ => false
  end.

Lemma eval_expr_get:
  forall vars s h e, 
              expcheck vars e = true ->
              varcompat vars s ->
              expr_get s h e = Some (eval e (locals2env s)).
Proof. induction e; simpl; auto; intros.
  apply H0 in H. unfold locals2env. 
 destruct (table_get s v); auto. congruence.
  specialize (IHe H H0). rewrite IHe. simpl.   f_equal; omega. 
  inv H.
Qed.

Lemma eval_expr_get_list:
  forall vars s h el, 
              forallb (expcheck vars) el = true ->
              varcompat vars s ->
              get_list s h el = Some (eval_list el (locals2env s)).
Proof. induction el; simpl; auto; intros.
 rewrite andb_true_iff in H; destruct H.
  rewrite (eval_expr_get vars s h a); auto. simpl.
  rewrite (IHel H1 H0); auto.
Qed.

Lemma varcompat_add:
  forall x vars z s, varcompat vars s -> varcompat (vs_add x vars) (table_set x z s).
Proof.
 intros. intros i ?. specialize (H i).
 unfold vs_mem, vs_add in *.
 apply ListSet.set_mem_correct1 in H0.
 destruct (eq_dec i x). 
 subst. rewrite table_gss. congruence.
 rewrite table_gso; auto. apply H.
 apply ListSet.set_add_elim2 in H0; auto.
 apply ListSet.set_mem_correct2; auto.
Qed.

Lemma varcompat_mk_locals:
  forall xl vl, length xl <= length vl -> varcompat xl (mk_locals xl vl).
Proof. 
 unfold varcompat, vs_mem, mk_locals. intros.
 revert vl H H0; induction xl; destruct vl; intros.
 apply ListSet.set_mem_correct1 in H0. inv H0.
 apply ListSet.set_mem_correct1 in H0. inv H0.
 inv H. simpl in H.
 specialize (IHxl vl). spec IHxl ; [ omega |].
 apply ListSet.set_mem_correct1 in H0. simpl in H0. destruct H0.
 subst. simpl. rewrite if_true; auto. congruence.
 simpl. destruct (eq_dec i a). congruence.
 apply IHxl. 
 apply ListSet.set_mem_correct2. auto.
Qed.

Definition inlist {A: Type}{EA: EqDec A} (x: A) (vl: list A) : bool :=
   existsb (fun y => if eq_dec x y then true else false) vl.

Lemma inlist_notIn {A: Type}{EA: EqDec A}:
  forall (x: A) (vl: list A), inlist x vl = false -> ~ In x vl.
Proof.
  induction vl; simpl; intros; intuition.
  subst. rewrite if_true in H by auto. inv H.
  destruct (eq_dec x a). inv H. simpl in H. auto.
Qed. 

Fixpoint list_nodups {A: Type}{EA: EqDec A} (vl: list A) : bool :=
  match vl with
  | nil => true
  | x::xl => andb (negb (inlist x xl)) (list_nodups xl)
  end.

Inductive list_norepet {A: Type} : list A -> Prop :=
  | list_norepet_nil:
      list_norepet nil
  | list_norepet_cons:
      forall hd tl,
      ~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).

Lemma nodups_norepet  {A: Type}{EA: EqDec A} :
    forall l, list_nodups l = true -> list_norepet l.
Proof. induction l; intros.
  constructor.
  simpl in H. apply andb_true_iff in H. 
  destruct H.
  constructor; auto.
  apply inlist_notIn. destruct (inlist a l); auto; inv H.
Qed.

(* SAFE FOR N STEPS *)

Definition safeN (p: program) (sk: state) (n: nat) : Prop :=
   exists sk', stepN p sk n = Some sk'.

Lemma stepN_plus: forall p sk1 n1 n2 sk3,
   stepN p sk1 (n1+n2) = Some sk3 <->
   (exists sk2, stepN p sk1 n1 = Some sk2 /\ stepN p sk2 n2 = Some sk3).
Proof.
 induction n1; intros. 
 simpl; split; eauto. intros [sk2 [? ?]]. inv H; auto.
 replace (S n1 + n2) with (n1 + S n2) by omega.
 rewrite (IHn1 (S n2) sk3).
 split; intros [sk2 [? ?]].
 simpl in H0; invSome.
 exists s. split; auto.
 replace (S n1) with (n1 + 1) by omega.
 rewrite (IHn1 1). exists sk2; split; simpl; auto. rewrite H0; auto.
 replace (S n1) with (n1 + 1) in H by omega.
 rewrite (IHn1 1) in H. destruct H as [sk4 [? ?]].
 exists sk4; split; simpl; auto. simpl in H1.  invSome. auto. 
Qed.

Lemma safeN_less: forall p sk n1 n2, n1 <= n2 -> safeN p sk n2 -> safeN p sk n1.
Proof.
 intros.
 assert (n2 = n1 + (n2-n1)) by omega.
 rewrite H1 in H,H0.
 forget (n2-n1) as k.
 clear n2 H1 H.
 destruct H0 as [sk' ?].
 rewrite stepN_plus in H.
 destruct H as [sk2 [? ?]]; exists sk2; auto.
Qed.

Lemma safeN_step:
  forall p sk sk' n, step p sk = Some sk' -> (safeN p sk (S n) <-> safeN p sk' n).
Proof.
  unfold safeN; intros.
  split; intros [sk2 ?].
  exists sk2.
 simpl in H0. rewrite H in H0. auto.
  exists sk2; simpl.  rewrite H; auto.
Qed.


(****** PROGRAM SAFETY AS A SEPARATION-LOGIC PREDICATE *)

Program Definition cohere (concrete: heap) : pred rmap :=
 fun w =>
 forall p v, heap_get (concrete) p = Some v  <->
                 w @ p = YES pfullshare (VAL v) NoneP.
Next Obligation.
  unfold hereditary; intros.
  rewrite H0. 
  apply age1_YES; auto.
Qed.


Program Definition assert_safe 
     (p: program) (vars: varset) (ctl: control) : assert :=
  fun s w => forall s' h, varcompat vars s' -> 
                   locals2env s' = s -> cohere h w -> safeN p (s',h,ctl) (level w).
 Next Obligation.
  unfold hereditary; intros.
  eapply safeN_less; [ | apply H0]; auto. subst.
  apply age_level in H.   rewrite H. change R.rmap with rmap. omega.
  clear - H H3. hnf in H3|-*. intros. rewrite H3.
    generalize (age1_YES _ _ p pfullshare (VAL v) H); intros.
  intuition.
 Qed.

Lemma assert_safe0: 
        forall p vars k s w, 
           (forall w', age w w' -> app_pred (assert_safe p vars k s) w) ->
            app_pred (assert_safe p vars k s) w.
Proof.
  intros.
  case_eq (age1 w); intros.
  apply (H _ H0).
  hnf; repeat intro.
  rewrite age1_level0 in H0. rewrite H0. hnf. econstructor; reflexivity.
Qed.

(******* FUNASSERT, MAKE_WORLD ********************)

Definition funspec := (list var * assert)%type.
Definition funspecs := table adr funspec.

Definition unpack (P: list adr -> pred rmap) (vl: listprod (@cons Type (list adr) nil)):  pred rmap := P (fst vl).

Definition call (P: list var * assert) (vl: list adr) : pred rmap := 
     (!! (length vl = length (fst P)) && snd P (arguments (fst P) vl)).

Program Definition cont (nP: funspec)  (v: adr) : pred rmap :=
  fun w => w @ v = PURE (FUN (fst nP)) (preds_fmap (approx (level w)) (SomeP (list adr::nil) 
             (unpack (call nP)))).
Next Obligation.
 intros; intro; intros.
  apply (age1_resource_at a a' H v (PURE (FUN (fst nP)) _));   simpl; auto.
Qed.

Definition funassert (G: funspecs) : pred rmap := 
   (All  i:_, All P:_,  !! (table_get G i = Some P) --> cont P i)  && 
   (All  i:_, All P:_,  cont P i --> !! exists P', table_get G i = Some P').

Definition make_world_aux (G: funspecs) (h: heap) (n: nat) (a: adr) : resource :=
   match table_get G a with
   | Some P => PURE (FUN (fst P))
                               (preds_fmap (approx n) 
                                      (SomeP (@cons Type (list adr) nil) (unpack (call P))))
   | None => match heap_get h a with
                     | Some v => YES pfullshare (VAL v) NoneP
                     | None => NO
                    end
   end.

Lemma make_world_aux_OK:
  forall G h n, 
         resource_fmap (approx n) oo make_world_aux G h n =  make_world_aux G h n.
Proof.
 intros.
 extensionality v; 
 unfold make_world_aux, compose.
 destruct (table_get G v). destruct f as [nargs P]. simpl.
 f_equal. f_equal. rewrite <- compose_assoc. rewrite approx_oo_approx. auto.
 destruct (heap_get h v); auto.
 unfold resource_fmap.
 f_equal. apply preds_fmap_NoneP.
Qed.  

Definition make_world (G: funspecs) (h: heap) (n: nat) : rmap :=
    proj1_sig (make_rmap (make_world_aux G h n) I n (make_world_aux_OK _ _ _)).

Lemma level_make_world:
  forall h G n, level (make_world G h n) = n.
Proof.
 intros; simpl.
 apply level_make_rmap.
Qed.

Inductive match_specs: forall (p: program) (G: funspecs), Prop :=
| match_specs_nil: match_specs nil nil
| match_specs_cons: forall i vars f p' P G',
         not (In i (map (@fst _ _) p')) ->
         match_specs p' G' ->
         typecheck vars f = true ->
         match_specs ((i,(vars,f))::p') ((i,P)::G').

Lemma match_specs_boundary:
   forall p G i, 
   match_specs p G -> i >= boundary p -> table_get G i = None.
Proof.
  induction 1. intros. reflexivity.
  intros. simpl in *. 
  destruct (@eq_dec adr _ i i0). subst.
  clear - H2. destruct (boundary p'). elimtype False; omega.
 generalize (Max.le_max_l i0 n); intro. elimtype False. omega.
 apply IHmatch_specs.
 destruct (boundary p'); try omega.
 generalize (Max.le_max_r i0 n0);  omega.
Qed.

Lemma funassert_e:  forall G i f,
      table_get G i = Some f -> 
      funassert G |-- cont f i.
Proof.
  intros.
  unfold funassert.
  apply andp_left1.
  intros w ?. apply H0; auto.
Qed.

Lemma funassert_make_world: forall p G n,
         app_pred (funassert G) (make_world G (initial_heap p) n).
Proof.
 intros ? ? ?.
 forget (initial_heap p) as h.
 split.
 intros i P w ? ?.
 hnf in H0.
 eapply pred_nec_hereditary; try apply H.
 clear w H.
 hnf. unfold make_world; simpl. rewrite resource_at_make_rmap.
 unfold make_world_aux. rewrite H0.
 f_equal. simpl. f_equal. rewrite level_make_rmap.
 reflexivity.
 intros i P w ? ?.
 hnf.
 case_eq (table_get G i); intros. eauto.
 elimtype False.
 hnf in H0.
 case_eq (make_world G h n @ i); intros.
 apply (necR_NO _ _ i H) in H2. inversion2 H0 H2.
 apply (necR_YES _ _ i _ _ _ H) in H2. inversion2 H2 H0.
 clear dependent w.
 unfold make_world in H2.
 rewrite resource_at_make_rmap in H2. unfold make_world_aux in H2.
 rewrite H1 in H2. destruct (heap_get h i); inv H2.
Qed.

Lemma cohere_make_world: 
  forall p G n,  
      match_specs p G ->
     app_pred (cohere (initial_heap p)) (make_world G (initial_heap p) n).
Proof.
 intros.
 hnf.
 intros. unfold make_world, make_world_aux; simpl. rewrite resource_at_make_rmap.
 unfold  initial_heap. simpl. unfold heap_get.
  rename p0 into i.
 destruct (lt_dec i (boundary p)).
 split; intro. inv H0. elimtype False.
 revert H0; case_eq (table_get G i); intros. destruct f as [nargs P].
 inv H1. inv H1.
 rewrite (match_specs_boundary p G i); auto; try omega.
 split; intro Hx; inv Hx; auto.
Qed.

Lemma funassert_get:
  forall G v nP,  funassert  G && cont nP v |--
                      Ex P':assert, (All vl:list adr, |> ! (call nP vl <=> call (fst nP,P') vl)) && !! (table_get G v = Some (fst nP,P')).
Proof.
 intros. intros w [? ?].
 destruct H.
 specialize (H v); specialize (H1 v).
 specialize (H1 _ _ (necR_refl _) H0).
 destruct H1 as [[args P'] ?].
 exists P'.
 specialize (H _ _ (necR_refl _) H1).
 split.
 Focus 2. hnf in H,H0. inversion2 H H0. apply H1.
 clear H1. rename H into H99. rename H0 into H97.
 hnf in H99,H97. rewrite H99 in H97.  apply PURE_inj in H97. destruct H97 as [H H97].
 simpl in H. destruct nP as [na P]. inv H.
 intro vl. intros w' ? w'' ?.
  assert (level w'' < level w). do 3 red in H. apply laterR_level in H. 
       apply le_lt_trans with (level w'); auto.
 simpl fst.
  split; intros w''' ? ?.  
 match type of H97 with ?A = _ => assert (app_pred (A (vl,tt)) w''') end.
  rewrite H97.
 split.
  change rmap with R.rmap in *.
  change ag_rmap with R.ag_rmap in *. 
  apply necR_level in H2; omega.
 apply H3.
  destruct H4. apply H5.
 match type of H97 with _ = ?A => assert (app_pred (A (vl,tt)) w''') end.
  rewrite <- H97.
 split.
  change rmap with R.rmap in *.
  change ag_rmap with R.ag_rmap in *. 
  apply necR_level in H2; omega.
 apply H3.
  destruct H4. apply H5.
Qed.

Lemma cont_core: forall P i w, app_pred (cont P i) w <-> app_pred (cont P i) (core w).
Proof.
 intros.
 unfold cont. simpl. rewrite <- core_resource_at.
 split; intro. rewrite H.
 clear. symmetry. rewrite level_core. apply unit_core; constructor.
 rewrite level_core in H.
 generalize (core_unit (w @ i)); intro.
 rewrite H in H0.
 inv H0; auto.
Qed.

Lemma funassert_core: forall G w, app_pred (funassert G) w <-> app_pred (funassert G) (core w).
Proof.
 intros.
 split; intros [? ?]; split; intros i P w' ? ?.
 specialize (H i P _ (necR_refl _) H2).
 apply cont_core in H. eapply pred_nec_hereditary; eauto.
 generalize (core_unit w); intro.
 unfold unit_for in H3.
 eapply nec_join in H3; eauto.
 destruct H3 as [y' [z' [? [? ?]]]].
 generalize (necR_linear' H4 H5); intro.
 spec H6. apply join_level in H3. destruct H3; congruence.
 subst z'. clear H5.
 specialize (H0 i P _ H4).
 apply join_core in H3. rewrite cont_core in H2. rewrite H3 in H2. rewrite <- cont_core in H2.
 specialize (H0 H2). apply H0.
 assert (necR (core w) (core w')).
 generalize (core_unit w); intro.
 unfold unit_for in H3.
 apply join_com in H3.
 eapply nec_join in H3; eauto.
 destruct H3 as [y' [z' [? [? ?]]]].
 generalize (necR_linear' H1 H5); intro.
 spec H6. apply join_level in H3. destruct H3; congruence. subst z'.
 apply join_com in H3.
 generalize (unit_identity _ H3); intro.
 apply identity_unit_equiv in H6. apply unit_core in H6.
 apply join_core in H3. rewrite H6 in H4. rewrite H3 in H4; auto.
 specialize (H i P _ H3 H2).
 apply cont_core in H; auto.
 assert (necR (core w) (core w')).
 generalize (core_unit w); intro.
 unfold unit_for in H3.
 apply join_com in H3.
 eapply nec_join in H3; eauto.
 destruct H3 as [y' [z' [? [? ?]]]].
 generalize (necR_linear' H1 H5); intro.
 spec H6. apply join_level in H3. destruct H3; congruence. subst z'.
 apply join_com in H3.
 generalize (unit_identity _ H3); intro.
 apply identity_unit_equiv in H6. apply unit_core in H6.
 apply join_core in H3. rewrite H6 in H4. rewrite H3 in H4; auto.
 specialize (H0 i P _ H3).
 apply H0. rewrite <- cont_core; auto.
Qed.


(**************** ALLOCPOOL ***************************)


Program Definition allocpool (b: adr) : pred rmap :=
   fun w => b>0 /\ forall i, if lt_dec i b then identity (w @ i) else w @ i = YES pfullshare (VAL 0) NoneP.
Next Obligation.
 intros. intro; intros.
  destruct H0; split; auto.
 intro i; specialize (H1 i).
 destruct (lt_dec i b).
  eapply age1_resource_at_identity; eauto.
 apply (age1_YES _ _ _ _ _ H); auto.
Qed.

Lemma allocpool_make_world: forall p G n,
          match_specs p G ->
          app_pred (allocpool (boundary p)) (make_world G (initial_heap p) n).
Proof.
  unfold make_world; intros.
  rename H into H'.
 unfold initial_locals,initial_heap  in *.
 split.
 destruct p; simpl. omega. destruct p. destruct (boundary p0); omega. 
 intro loc.
 destruct (make_rmap
        (make_world_aux G
           (fun i : adr => if lt_dec i (boundary p) then None else Some 0) n)
        I n
        (make_world_aux_OK G
           (fun i : adr => if lt_dec i (boundary p) then None else Some 0) n)) as [? [? ?]];
  simpl in *. rewrite e0. unfold make_world_aux.
 unfold heap_get.
 destruct (lt_dec loc (boundary p)).
 destruct (table_get G loc);  apply identity_resource; auto.
 rewrite (match_specs_boundary p G loc); auto.
 omega.
Qed.

Lemma alloc: forall b, allocpool b = ((!! (b > 0) && mapsto b 0) * allocpool (S b)).
Proof.
 intros. apply pred_ext.
  intros w ?.
 destruct H as [H' H]. 
  destruct (deallocate w 
                   (fun i => if lt_dec b i then NO else w @ i) 
                   (fun i => if eq_dec b i then NO else w @ i)
               I I) as [w1 [w2 [? ?]]].
 intro l; specialize (H l).
 destruct (eq_dec b l). subst. rewrite if_false by omega. rewrite if_false in H by omega.
 rewrite H; constructor.
 destruct (lt_dec b l).
 rewrite if_false in H by omega.
 rewrite H; constructor.
 rewrite if_true in H.
 apply identity_unit_equiv in H. apply H.
 unfold adr in *; omega.
 exists w1; exists w2; split3; auto.
 split; auto.
 intro i. apply (resource_at_join _ _ _ i) in H0. specialize (H i). rewrite H1 in *.
 clear w1 H1.
 destruct (lt_dec b i).
 rewrite if_false by omega. apply NO_identity.
 destruct (eq_dec i b). subst. rewrite if_false in H by omega. auto.
 rewrite if_true in H. auto.
 unfold adr in *; omega.
 split. omega.
 intro i. apply (resource_at_join _ _ _ i) in H0. specialize (H i). rewrite H1 in *.
 clear w1 H1.
 destruct (lt_dec b i).
 rewrite if_false by omega. rewrite if_false in H by omega. rewrite H in H0. inv H0; auto.
 rewrite if_true by omega.
 destruct (eq_dec i b). subst. rewrite if_false in H by omega. rewrite H in H0; inv H0; auto.
 apply NO_identity. pfullshare_join.
 rewrite if_true in H by (unfold adr in *; omega).
 apply H in H0. rewrite H0; auto.

  intros w [w1 [w2 [? [? ?]]]].
  destruct H0 as [H0' H0]. destruct H1 as [_ H1].
 split; auto.
  intro i. specialize (H0 i); specialize (H1 i). apply (resource_at_join _ _ _ i) in H.
  destruct (lt_dec i b). rewrite if_true in H1 by omega.
  rewrite if_false in H0 by omega. apply H0 in H. rewrite <- H; auto.
  destruct (@eq_dec adr _ i b). subst. rewrite H0 in H. rewrite if_true in H1 by omega.
  apply join_com in H. apply H1 in H. auto.
  rewrite if_false in H1. rewrite H1 in H. apply H0 in H. auto.
  unfold AV.address, AV0.address, adr in *. omega.
Qed.

(******** THIS SHOULD GO IN msl/predicates_hered.v *)
Lemma prop_right {A}{agA: ageable A} : forall (P: pred A) (Q: Prop), Q -> P |-- prop Q.
Proof. repeat intro; auto.
Qed.