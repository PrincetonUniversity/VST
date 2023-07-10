Require Import VST.floyd.base2.
Require Export VST.floyd.canon.
Import LiftNotation.

Ltac refold_right_sepcon R :=
 match R with
 | bi_sep ?R1 ?R' => let S := refold_right_sepcon R' in constr: (R1 :: S )
 | _ => constr:(R :: nil)
 end.

Section mpred.

Context `{!heapGS Σ}.

Lemma SEP_entail:
 forall R' Delta P Q R,
   (fold_right_sepcon R ⊢ fold_right_sepcon R') ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
rewrite bi.and_elim_r /PROPx /LOCALx /SEPx H //.
Qed.

Lemma SEP_entail':
 forall R' Delta P Q R,
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ ⎡fold_right_sepcon R'⎤ ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
apply bi.and_intro, bi.and_intro; [iIntros "(_ & $ & _)" | iIntros "(_ & _ & $ & _)" | apply H].
Qed.

Lemma SEP_entail'_fupd:
 forall R' E Delta P Q R,
   (ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ |={E}=> ⎡fold_right_sepcon R'⎤) ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ |={E}=> PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
iIntros "(#? & #? & #? & H)"; iFrame "#".
iApply H; iFrame; auto.
Qed.

Arguments sem_cmp c !t1 !t2 / v1 v2.

Lemma lift0_unfold: forall {A} (f: A)  rho,  lift0 f rho = f.
Proof. reflexivity. Qed.

Lemma lift0_unfoldC: forall {A} (f: A) (rho: environ),  `f rho = f.
Proof. reflexivity. Qed.

Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift1_unfoldC: forall {A1 B} (f: A1 -> B) a1 (rho: environ),
        `f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfoldC: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        `f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfold: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        lift3 f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfoldC: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        `f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfold: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        lift4 f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfoldC: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        `f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Lemma alift0_unfold: forall {A} (f: A)  rho,  alift0 f rho = f.
Proof. reflexivity. Qed.

Lemma alift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        alift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma alift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: argsEnviron),
        alift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma alift3_unfold: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: argsEnviron),
        alift3 f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma alift4_unfold: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: argsEnviron),
        alift4 f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Lemma subst_lift0: forall {A} id v (f: A),
        subst id v (lift0 f) = lift0 f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0': forall {A} id v (f: A),
        subst id v (fun _ => f) = (fun _ => f).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0C:
  forall {B} id (v: environ -> val) (f: B) ,
          subst id v (`f) = `f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1:
  forall {A1 B} id v (f: A1 -> B) a,
          subst id v (lift1 f a) = lift1 f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1':
  forall {A1 B} id v (f: A1 -> B) a,
          subst id v (fun rho => f (a rho)) = fun rho => f (subst id v a rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1C:
  forall {A1 B} id (v: environ -> val) (f: A1 -> B) (a: environ -> A1),
          subst id v (`f a)  = `f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2:
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b,
          subst id v (lift2 f a b) = lift2 f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2':
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b,
          subst id v (fun rho => f (a rho) (b rho)) = fun rho => f (subst id v a rho) (subst id v b rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2C:
  forall {A1 A2 B} id (v: environ -> val) (f: A1 -> A2 -> B) (a: environ -> A1) (b: environ -> A2),
          subst id v (`f a b) = `f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3:
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3,
          subst id v (lift3 f a1 a2 a3) = lift3 f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3':
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3,
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho)) =
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3C:
  forall {A1 A2 A3 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> B)
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3),
          subst id v (`f a1 a2 a3) = `f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4:
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4,
          subst id v (lift4 f a1 a2 a3 a4) = lift4 f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4':
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4,
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho) (a4 rho)) =
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho) (subst id v a4 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4C:
  forall {A1 A2 A3 A4 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> A4 -> B)
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3) (a4: environ -> A4),
          subst id v (`f a1 a2 a3 a4) = `f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma bool_val_int_eq_e:
  forall i j m, Cop.bool_val (Val.of_bool (Int.eq i j)) type_bool m = Some true ->
    i=j.
Proof.
 intros.
 unfold Cop.bool_val in H.
 destruct Archi.ptr64 eqn:Hp;
 revert H; case_eq (Val.of_bool (Int.eq i j)); simpl; intros; inv H0.
+
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. rewrite Int.eq_true in H2. inv H2.
+
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. inv H2.
+ unfold Val.of_bool in H.  destruct (Int.eq i j); inv H.
Qed.

Lemma bool_val_notbool_ptr:
    forall v t m,
   match t with Tpointer _ _ => True | _ => False end ->
   (Cop.bool_val (force_val (Cop.sem_notbool v t m)) type_bool m = Some true)
        = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 unfold Cop.sem_notbool, Cop.bool_val, Val.of_bool, Cop.classify_bool, nullval.
 destruct Archi.ptr64 eqn:Hp; simpl;
 apply prop_ext; split; intros.
-
 destruct v; simpl in H; try solve [inv H].
 destruct (Int64.eq i Int64.zero) eqn:?; inv H.
  apply expr_lemmas.int64_eq_e in Heqb. subst; reflexivity.
 destruct (Memory.Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:?;
  simpl in H; inv H.
-
  subst v; simpl. reflexivity.
-
 destruct v; simpl in H; try solve [inv H].
 destruct (Int.eq i Int.zero) eqn:?; inv H.
  apply int_eq_e in Heqb. subst; reflexivity.
 destruct (Memory.Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:?;
  simpl in H; inv H.
-
  subst v; simpl. reflexivity.
Qed.

Definition retval : environ -> val := eval_id ret_temp.

Lemma simpl_get_result1:
 forall (f: val -> Prop) i, @liftx (Tarrow environ (LiftEnviron Prop)) (@liftx (Tarrow val (LiftEnviron Prop))f retval) (get_result1 i) = `f (eval_id i).
Proof.
intros; extensionality rho.
unfold_lift; unfold retval, get_result1.
f_equal.
Qed.

Lemma retval_get_result1:
   forall i rho, retval (get_result1 i rho) = (eval_id i rho).
Proof. intros. unfold retval, get_result1. simpl.
 normalize.
Qed.

Lemma retval_ext_rval:
  forall ge t v, retval (make_ext_rval ge t v) = force_val v.
Proof.
 intros. unfold retval, eval_id; simpl. unfold make_ext_rval; simpl.
destruct t eqn:?H;  destruct v eqn:?H; simpl; auto.
Abort.

Lemma retval_lemma1:
  forall rho v,     retval (env_set rho ret_temp v) = v.
Proof.
 intros. unfold retval.  normalize.
Qed.

Lemma retval_make_args:
  forall v rho, retval (make_args (ret_temp::nil) (v::nil) rho) = v.
Proof. intros.  unfold retval, eval_id; simpl. try rewrite Map.gss. reflexivity.
Qed.

(*Lemma andp_makeargs:
   forall (a b: assert) d e,
   `(a ∧ b) (make_args d e) = `a (make_args d e) ∧ `b (make_args d e).
Proof. intros. reflexivity. Qed.

Lemma local_makeargs:
   forall (f: val -> Prop) v,
   `(local (`(f) retval)) (make_args (cons ret_temp nil) (cons v nil))
    = (local (`(f) `(v))).
Proof. intros. reflexivity. Qed.

Lemma simpl_and_get_result1:
  forall (Q R: assert) i,
    `(Q ∧ R) (get_result1 i) = `Q (get_result1 i) ∧ `R (get_result1 i).
Proof. intros. reflexivity. Qed.

Lemma liftx_local_retval:
  forall (P: val -> Prop) i,
   `(local (`P retval)) (get_result1 i) = local (`P (eval_id i)).
Proof. intros. reflexivity. Qed.*)

Lemma Vint_inj': forall i j,  (Vint i = Vint j) =  (i=j).
Proof. intros; apply prop_ext; split; intro; congruence. Qed.

Notation assert := (@assert Σ).

Lemma overridePost_normal_right:
  forall (P Q : assert) R,
   (P ⊢ Q) ->
   P ⊢ RA_normal (overridePost Q R).
Proof.
  intros.
  destruct R; simpl; auto.
Qed.

Fixpoint fold_right_and P0 (l: list Prop) : Prop :=
 match l with
 | nil => P0
 | b::r => b  /\ fold_right_and P0 r
 end.

Fixpoint fold_right_and_True (l: list Prop) : Prop :=
 match l with
 | nil => True
 | b :: nil => b
 | b::r => b /\ fold_right_and_True r
 end.

Definition fold_right_PROP_SEP (l1: list Prop) (l2: list mpred) : mpred :=
 match l1 with
 | nil => fold_right_sepcon l2
 | l => ⌜fold_right_and_True l⌝ ∧ fold_right_sepcon l2
 end.

Lemma fold_right_PROP_SEP_spec: forall l1 l2,
  fold_right_PROP_SEP l1 l2 ⊣⊢ ⌜fold_right and True l1⌝ ∧ fold_right_sepcon l2.
Proof.
  intros.
  assert (fold_right_and_True l1 <-> fold_right and True%type l1).
  { destruct l1; [tauto |].
    revert P; induction l1; intros.
    - simpl; tauto.
    - change (P /\ fold_right_and_True (a :: l1) <-> P /\ fold_right and True%type (a :: l1)).
      specialize (IHl1 a).
      tauto. }
  destruct l1.
  + rewrite /= bi.True_and //.
  + unfold fold_right_PROP_SEP.
    rewrite H.
    auto.
Qed.

Lemma typed_true_isptr:
 forall t, match t with Tpointer _ _ => True | Tarray _ _ _ => True | Tfunction _ _ _ => True | _ => False end ->
          typed_true t = isptr.
Proof.
intros. extensionality x; apply prop_ext.
unfold typed_true, bool_val, strict_bool_val, isptr.
destruct t; try contradiction;
destruct Archi.ptr64 eqn:Hp;
destruct x; try tauto; intuition (try congruence);
revert H0; simple_if_tac; intro H0; inv H0.
Qed.

Lemma tc_eval'_id_i:
  forall Delta t i rho,
               tc_environ Delta rho ->
              (temp_types Delta)!!i = Some t ->
              tc_val' t (eval_id i rho).
Proof.
intros.
unfold tc_environ in H.
destruct rho.
destruct H as [? _].
destruct (H i t H0) as [v [? ?]].
unfold eval_id. simpl in *. rewrite H1. simpl; auto.
Qed.

Lemma is_int_e:
 forall v i s , is_int i s v -> exists n, v = Vint n /\ is_int i s v.
Proof.
intros.
 destruct i,s,v; try inv H; simpl; eauto.
Qed.

Definition reflect_temps_f (rho: environ) (b: Prop) (i: ident) (t: type) : Prop :=
  tc_val' t (eval_id i rho) /\ b.

Definition reflect_temps (Delta: tycontext) (rho: environ) : Prop :=
    Maps.PTree.fold (reflect_temps_f rho) (temp_types Delta) True%type.

Lemma reflect_temps_valid:
  forall Delta rho,
    tc_environ Delta rho -> reflect_temps Delta rho.
Proof.
intros.
unfold reflect_temps.
rewrite Maps.PTree.fold_spec.
remember  (Maps.PTree.elements (temp_types Delta)) as el.
assert (forall i v, In (i,v) el -> (temp_types Delta) !! i = Some v).
 intros. subst el. apply Maps.PTree.elements_complete; auto.
clear Heqel.
assert (forall b: Prop, b -> fold_left
  (fun (a : Prop) (p : positive * type) =>
   reflect_temps_f rho a (fst p) (snd p)) el b);
  [ | auto].
revert H0; induction el; simpl; intros; auto.
unfold reflect_temps_f at 2.
destruct a as [i t]; simpl; auto.
apply IHel; auto.
split; auto.
eapply tc_eval'_id_i.
eassumption.
apply H0; auto.
Qed.

Lemma is_true_negb:
 forall a, is_true (negb a) -> a=false.
Proof.
destruct a; auto; try contradiction.
Qed.

Lemma sem_cast_pointer2':
  forall (v : val) (t1 t2: type),
  (match t1 with
  | Tpointer _ _ => is_true (negb (eqb_type t1 int_or_ptr_type))
  | Tint I32 _ _ => if Archi.ptr64 then False else True
  | Tlong _ _ => if Archi.ptr64 then True else False
  | _ => False end)%type ->
  (match t2 with
  | Tpointer _ _ => is_true (negb (eqb_type t2 int_or_ptr_type))
  | Tint I32 _ _ => if Archi.ptr64 then False else True
  | Tlong _ _ => if Archi.ptr64 then True else False
  | _ => False end)%type ->
  is_pointer_or_null v -> force_val (sem_cast t1 t2 v) = v.
Proof.
intros.
unfold sem_cast, classify_cast, force_val; simpl.
destruct Archi.ptr64 eqn:Hp;
destruct t1; try contradiction; try destruct i; try contradiction; auto;
destruct t2; try contradiction; try destruct i; try contradiction; auto;
try rewrite (is_true_negb _ H); try rewrite (is_true_negb _ H0);
destruct v; inv H1; auto.
Qed.

Lemma sem_cast_pointer2:
  forall v t1 t2 t3 t1' t2',
   t1' = Tpointer t1 noattr ->
   t2' = Tpointer t2 noattr ->
   tc_val (Tpointer t3 noattr) v ->
   force_val (sem_cast t1' t2' v) = v.
Proof.
intros.
subst.
hnf in H1.
simpl in H1. rewrite andb_false_r in H1.
unfold sem_cast, classify_cast; simpl.
reflexivity.
Qed.

Lemma force_eval_var_int_ptr :
forall  {cs: compspecs}  Delta rho i t,
tc_environ Delta rho ->
tc_lvalue Delta (Evar i t) rho ⊢
        ⌜force_val
            match eval_var i t rho with
            | Vptr _ _ => Some (eval_var i t rho)
            | _ => None
            end = eval_var i t rho⌝.
Proof.
intros.
rewrite typecheck_lvalue_sound //.
apply bi.pure_mono; simpl; intros.
unfold eval_var in *.
destruct (Map.get (ve_of rho) i) as [[? ?] |].
destruct (eqb_type t t0); try discriminate; reflexivity.
destruct (Map.get (ge_of rho) i).
reflexivity.
inv H0.
Qed.

Lemma is_pointer_or_null_force_int_ptr:
   forall v, is_pointer_or_null v -> (force_val
        match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
        end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Lemma is_pointer_force_int_ptr:
   forall v, isptr v -> (force_val
        match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
        end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Lemma is_pointer_or_null_match :
   forall v, is_pointer_or_null v ->
        (match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
         end) = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Lemma is_pointer_force_int_ptr2:
   forall v, isptr v ->
        match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
         end = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Lemma is_pointer_or_null_force_int_ptr2:
   forall v, is_pointer_or_null (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) -> (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Lemma isptr_match : forall w0,
is_pointer_or_null
         match
           match w0 with
          | Vint _ => if Archi.ptr64 then None else Some w0
          | Vlong _ => if Archi.ptr64 then Some w0 else None
          | Vptr _ _ => Some w0
           | _ => None
           end
         with
         | Some v' => v'
         | None => Vundef
         end
= is_pointer_or_null w0.
intros.
unfold is_pointer_or_null.
destruct Archi.ptr64 eqn:Hp;
destruct w0; auto.
Qed.


Lemma eval_cast_neutral_tc_val:
   forall v, (exists t, tc_val t v /\ is_pointer_type t = true) ->
       sem_cast_pointer v = Some v.
Proof.
intros.
destruct H as [t [? ?]].
hnf in H.
unfold is_pointer_type in H0.
unfold sem_cast_pointer.
destruct (eqb_type t int_or_ptr_type);
destruct t,v; inv H0; inv H; reflexivity.
Qed.

Lemma eval_cast_neutral_is_pointer_or_null:
   forall v, is_pointer_or_null v -> sem_cast_pointer v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Lemma is_pointer_or_null_eval_cast_neutral:
  forall v, is_pointer_or_null (force_val (sem_cast_pointer v)) = is_pointer_or_null v.
Proof. destruct v; reflexivity. Qed.

Lemma eval_cast_neutral_isptr:
   forall v, isptr v -> sem_cast_pointer v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Notation assert_of := (@assert_of Σ).

Lemma raise_sepcon:
 forall A B : assert,
    assert_of (fun rho: environ => A rho ∗ B rho) ⊣⊢ (A ∗ B).
Proof. split => rho; monPred.unseal; done. Qed.

Lemma lift1_lift1_retval {A}: forall i (P: val -> A),
lift1 (lift1 P retval) (get_result1 i) = lift1 P (eval_id i).
Proof. intros.  extensionality rho.
  unfold lift1.  f_equal; normalize.
Qed.

Lemma lift_lift_retval:
  forall (i: ident) P,
   @liftx (Tarrow environ (LiftEnviron mpred))
     (@liftx (Tarrow val (LiftEnviron mpred)) P retval) (get_result1 i) = `P (eval_id i).
Proof.
 reflexivity.
Qed.

Lemma lift_lift_x:  (* generalizes lift_lift_val *)
  forall t t' P (v: t),
  (@liftx (Tarrow t (LiftEnviron t')) P (@liftx (LiftEnviron t) v)) =
  (@liftx (LiftEnviron t') (P v)).
Proof. reflexivity. Qed.

Lemma lift0_exp:
  forall (B: Type) (f: B -> mpred), assert_of (lift0 (∃ x, f x)) ⊣⊢ ∃ x:B, assert_of (lift0 (f x)).
Proof.
  split => rho; rewrite /lift0; simpl; monPred.unseal; done.
Qed.

Lemma lift0C_exp:
  forall (B: Type) (f: B -> mpred), assert_of (`(∃ x, f x)) ⊣⊢ ∃ x:B, assert_of (`(f x)).
Proof.
  split => rho; unfold_lift; simpl; monPred.unseal; done.
Qed.

Lemma lift0_andp:
 forall P Q,
   assert_of (lift0 (P ∧ Q)) ⊣⊢ assert_of (lift0 P) ∧ assert_of (lift0 Q).
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0C_andp:
 forall P Q,
  assert_of `(P ∧ Q) ⊣⊢ assert_of (`P) ∧ assert_of (`Q).
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0_prop:
 forall P : Prop, assert_of (lift0 ⌜P⌝) ⊣⊢ ⌜P⌝.
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0C_prop:
 forall P : Prop, assert_of (`⌜P⌝) ⊣⊢ ⌜P⌝.
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0_sepcon:
 forall P Q,
  assert_of (lift0 (P ∗ Q)) ⊣⊢ assert_of (lift0 P) ∗ assert_of (lift0 Q).
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0C_sepcon:
 forall P Q,
  assert_of (` (P ∗ Q)) ⊣⊢ assert_of (`P) ∗ assert_of (`Q).
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0_later:
  forall P,
   assert_of (lift0 (▷ P)) ⊣⊢ ▷ assert_of (lift0 P).
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma lift0C_later:
  forall P,
   assert_of (`(▷ P)) ⊣⊢ ▷ assert_of (`P).
Proof.
  split => rho; monPred.unseal; done.
Qed.

Lemma fst_unfold: forall {A B} (x: A) (y: B), fst (x,y) = x.
Proof. reflexivity. Qed.
Lemma snd_unfold: forall {A B} (x: A) (y: B), snd (x,y) = y.
Proof. reflexivity. Qed.

Lemma derives_extract_PROP :
  forall {B} (P1: Prop) A P QR S,
     (P1 -> A ∧ PROPx P QR ⊢ S) ->
     A ∧ @PROPx B Σ (P1::P) QR ⊢ S.
Proof.
unfold PROPx in *.
intros.
rewrite fold_right_cons.
normalize.
rewrite -H //; monPred.unseal.
normalize.
Qed.

Notation local := (@local Σ).

Lemma local_andp_prop:  forall P Q, local P ∧ ⌜Q⌝ ⊣⊢ ⌜Q⌝ ∧ local P.
Proof. intros. apply bi.and_comm. Qed.
Lemma local_andp_prop1: forall P Q R, local P ∧ (⌜Q⌝ ∧ R) ⊣⊢ ⌜Q⌝ ∧ (local P ∧ R).
Proof. intros. rewrite bi.and_comm. rewrite -bi.and_assoc. f_equiv. apply bi.and_comm. Qed.

Lemma local_sepcon_assoc1:
   forall P Q R, (local P ∧ Q) ∗ R ⊣⊢ local P ∧ (Q ∗ R).
Proof.
  intros; rewrite bi.persistent_and_sep_assoc //.
Qed.
Lemma local_sepcon_assoc2:
   forall P Q R, R ∗ (local P ∧ Q) ⊣⊢ local P ∧ (R ∗ Q).
Proof.
  intros; rewrite persistent_and_sep_assoc' //.
Qed.

Definition do_canon (x y : assert) := x ∗ y.

Lemma andp_later_derives:
  forall {B : bi} (P Q P' Q' : B), (P ⊢ ▷ P') -> (Q ⊢ ▷ Q') -> P ∧ Q ⊢ ▷ (P' ∧ Q').
Proof.
  intros ????? -> ->; auto.
Qed.

Lemma sepcon_later_derives:
  forall {B : bi} (P Q P' Q': B), (P ⊢ ▷ P') -> (Q ⊢ ▷ Q') -> P ∗ Q ⊢ ▷ (P' ∗ Q').
Proof.
  intros ????? -> ->; auto.
Qed.

(* Definitions of convertPre and mk_funspec' are to support
  compatibility with old-style funspecs (see funspec_old.v) *)
Definition convertPre' (f: funsig) A
  (Pre: A -> assert)  (w: A) (ae: argsEnviron) : mpred :=
 ⌜length (snd ae) = length (fst f)⌝ ∧
 Pre w (make_args (map fst (fst f)) (snd ae)
    (mkEnviron (fst ae) (Map.empty (block*type)) (Map.empty val))).

Definition convertPre f A Pre w := argsassert_of (convertPre' f A Pre w).

Definition mk_funspec' (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> assert): funspec :=
  NDmk_funspec (typesig_of_funsig f) cc
  A (convertPre f A Pre) Post.

Fixpoint split_as_gv_temps (l: list localdef) : option ((list globals) * (list (ident * val))) :=
  match l with
    nil => Some (nil, nil)
  | temp i v :: l' => match split_as_gv_temps l' with
                        None => None
                      | Some (gvs, temps) => Some (gvs, (i,v)::temps)
                      end
  | lvar i t v :: l' => None
  | gvars g :: l' =>  match split_as_gv_temps l' with
                        None => None
                      | Some (gvs, temps) => Some (g::gvs, temps)
                      end
end.

Definition ImpossibleFunspec :=
   NDmk_funspec (nil,Tvoid) cc_default (Impossible)
        (fun _ => False : @argsassert Σ) (fun _ => False : assert).

Lemma prop_true_andp1 :
  forall {B : bi} (P1 P2: Prop) (Q : B),
    P1 -> ⌜P1 /\ P2⌝ ∧ Q ⊣⊢ ⌜P2⌝ ∧ Q.
Proof.
  intros; rewrite bi.pure_and bi.pure_True // bi.True_and //.
Qed.

Lemma and_assoc': forall A B C: Prop,
  ((A /\ B) /\ C) = (A /\ (B /\ C)).
Proof.
intros. apply prop_ext; symmetry; apply and_assoc.
Qed.

Definition splittablex (A: Prop) := True%type.

Lemma and_assoc_splittablex: forall {BI : bi} (A B C: Prop),
    splittablex (A /\ B) ->
  (⌜(A /\ B) /\ C⌝ : BI) ⊣⊢ ⌜A /\ (B /\ C)⌝.
Proof.
intros. rewrite and_assoc'; auto.
Qed.

Lemma and_assoc'': forall {BI : bi} (A B C: Prop),
  (⌜(A /\ B) /\ C⌝ : BI) ⊣⊢ ⌜A /\ (B /\ C)⌝.
Proof.
intros. rewrite and_assoc'; auto.
Qed.

Lemma semax_later_trivial: forall {Espec} `{!externalGS OK_ty Σ} {cs: compspecs} E Delta P c Q,
  semax E Delta (▷ P) c Q ->
  semax E Delta P c Q.
Proof.
 intros until Q.
 apply semax_pre0; auto.
Qed.

Lemma prop_and1:
  forall {BI : bi} (P Q : Prop), P -> (⌜P /\ Q⌝ : BI) ⊣⊢ ⌜Q⌝.
Proof.
 intros. f_equiv; tauto.
Qed.

Lemma subst_make_args':
  forall  {cs: compspecs}  id v (P: assert) fsig tl el,
  length tl = length el ->
  length (fst fsig) = length el ->
  assert_of (subst id v (fun rho => P (make_args' fsig (eval_exprlist tl el) rho))) ⊣⊢
           assert_of (fun rho => P (make_args' fsig (subst id v (eval_exprlist tl el)) rho)).
Proof.
  split => rho; rewrite /subst; simpl.
  f_equiv. unfold make_args'.
  revert tl el H H0; induction (fst fsig); destruct tl,el; simpl; intros; inv H; inv H0.
  reflexivity.
  specialize (IHl _ _ H2 H1).
  unfold_lift; rewrite IHl. auto.
Qed.

Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.


Definition rlt_ident_eq := ident_eq.  (* for convenience in selectively simplifying *)

Fixpoint remove_localdef_temp (i: ident) (l: list localdef) : list localdef :=
  match l with
  | nil => nil
  | d :: l0 =>
     let rest := remove_localdef_temp i l0 in
     match d with
     | temp j v =>
       if rlt_ident_eq i j
       then rest
       else d :: rest
     | _ => d :: rest
     end
  end.

Lemma subst_stackframe_of:
  forall {cs: compspecs} i v f, assert_of (subst i v (stackframe_of f)) ⊣⊢ stackframe_of f.
Proof.
  unfold stackframe_of; simpl; intros.
  unfold subst.
  split => rho; simpl.
  induction (fn_vars f); simpl; [|revert IHl]; monPred.unseal; first done; intros.
  rewrite IHl; f_equiv.
  rewrite /var_block; monPred.unseal; done.
Qed.

Lemma remove_localdef_temp_PROP: forall (i: ident) P Q R,
  (∃ old: val, assert_of (subst i `(old) (PROPx P (LOCALx Q (SEPx R))))) ⊢
  PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)).
Proof.
  intros.
  split => rho; rewrite /subst /PROPx /LOCALx /SEPx; monPred.unseal.
  iIntros "(% & $ & H & $)".
  iSplit; last done.
  iApply (bi.pure_mono with "H").
  induction Q; simpl fold_right.
  + autorewrite with subst norm; auto.
  + intros (? & ?%IHQ).
    unfold locald_denote in H.
    destruct a; [if_tac | ..];
    autorewrite with subst norm; simpl; super_unfold_lift; auto.
    split; auto.
    rewrite eval_id_other // in H.
Qed.

Lemma eval_id_denote_tc_initialized: forall Delta i t v,
  (temp_types Delta) !! i = Some t ->
  local (tc_environ Delta) ∧ local (`and (`(eq v) (eval_id i)) `(v <> Vundef)) ⊢ assert_of (denote_tc_initialized i t).
Proof.
  intros.
  split => rho; rewrite /local /lift1; monPred.unseal; unfold_lift.
  iIntros "((%TC & % & %) & %Hv & %)"; iPureIntro.
  destruct (TC _ _ H) as (? & Hi & Ht).
  rewrite /eval_id Hi in Hv; simpl in *; subst; eauto.
Qed.

Lemma PQR_denote_tc_initialized: forall Delta i t v P Q R,
  (temp_types Delta) !! i = Some t ->
  local (tc_environ Delta) ∧ PROPx P (LOCALx (temp i v :: Q) R) ⊢ assert_of (denote_tc_initialized i t).
Proof.
  intros.
  rewrite -eval_id_denote_tc_initialized //.
  apply bi.and_mono; first done.
  rewrite <- insert_local'.
  rewrite bi.and_elim_l //.
Qed.

Notation LOCALx := (@LOCALx Σ).

Lemma derives_remove_localdef_PQR: forall P Q R i,
  PROPx P (LOCALx Q (SEPx R)) ⊢ PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)).
Proof.
  intros.
  go_lowerx.
  apply bi.and_intro; auto.
  apply bi.pure_intro.
  clear H; rename H0 into H.
  induction Q; simpl in *; auto.
  destruct a; try now (destruct H; simpl in *; split; auto).
  destruct H.
  if_tac; simpl in *; auto.
Qed.

Lemma subst_remove_localdef_PQR: forall P Q R i v,
  assert_of (subst i v (PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)))) ⊢ PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)).
Proof.
  intros.
  go_lowerx.
  apply bi.and_intro; auto.
  apply bi.pure_intro.
  clear H; rename H0 into H.
  induction Q; simpl in *; auto.
  destruct a; try now (destruct H; simpl in *; split; auto).
  if_tac; simpl in *; auto.
  destruct H; split; auto.
  unfold_lift in H.
  destruct H; subst.
  unfold_lift. rewrite -> eval_id_other in * by auto.
  auto.
Qed.

Fixpoint iota_formals (i: ident) (tl: typelist) :=
 match tl with
 | Tcons t tl' => (i,t) :: iota_formals (i+1)%positive tl'
 | Tnil => nil
 end.

Lemma isptr_force_ptr'' : forall p Q,
    (isptr p -> Q) ->
    (isptr (force_ptr p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply Coq.Init.Logic.I.
Qed.

Lemma isptr_offset_val'': forall i p Q,
    (isptr p -> Q) ->
    (isptr (offset_val i p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply Coq.Init.Logic.I.
Qed.

Lemma ptr_eq_e': forall v1 v2 B,
   (v1=v2 -> B) ->
   (ptr_eq v1 v2 -> B).
Proof.
intuition. apply X. apply ptr_eq_e; auto.
Qed.

Lemma typed_false_of_bool':
 forall x (P: Prop),
    ((x=false) -> P) ->
    (typed_false tint (bool2val x) -> P).
Proof.
intuition.
apply H, typed_false_of_bool; auto.
Qed.

Lemma typed_true_of_bool':
 forall x (P: Prop),
    ((x=true) -> P) ->
    (typed_true tint (bool2val x) -> P).
Proof.
intuition.
apply H, typed_true_of_bool; auto.
Qed.

Lemma saturate_aux20:
 forall (P Q: mpred) P' Q' ,
    (P ⊢ ⌜P'⌝) ->
    (Q ⊢ ⌜Q'⌝) ->
    P ∗ Q ⊢ ⌜P' /\ Q'⌝.
Proof.
intros ???? -> ->; auto.
Qed.

Lemma saturate_aux21x:
  forall (P Q S: mpred),
   (P ⊢ S) ->
   (S ∧ P ⊢ Q) -> P ⊢ Q.
Proof.
intros ???? <-; auto.
Qed.

Lemma prop_right_emp:
 forall {BI : bi} (P: Prop), P -> (emp : BI) ⊢ ⌜P⌝.
Proof. intros. normalize. Qed.

Lemma prop_and_right:
 forall {BI : bi} (U: BI) (X Y: Prop),
    X ->
    (U ⊢ ⌜Y⌝) ->
    U ⊢ ⌜X /\ Y⌝.
Proof. intros ????? ->; auto. Qed.

Lemma fold_right_sepcon_subst:
 forall i e (R : list assert), fold_right bi_sep emp (map (fun r : assert => assert_of (subst i e r)) R) ⊣⊢ assert_of (subst i e (fold_right bi_sep emp R)).
Proof.
 intros. induction R; simpl; first by monPred.unseal.
 autorewrite with subst. f_equiv; auto.
Qed.

Lemma unsigned_eq_eq: forall i j, Int.unsigned i = Int.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Int.repr_unsigned i), <- (Int.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

Lemma prop_false_andp:
 forall {BI : bi} P (Q : BI), ~P -> ⌜P⌝ ∧ Q ⊣⊢ False.
Proof.
  intros; rewrite bi.pure_False // bi.False_and //.
Qed.

Lemma wand_join:
  forall {BI : bi} (x1 x2 y1 y2: BI),
    (x1 -∗ y1) ∗ (x2 -∗ y2) ⊢ ((x1 ∗ x2) -∗ (y1 ∗ y2)).
Proof.
  intros; iIntros "(H1 & H2) (? & ?)".
  iPoseProof ("H1" with "[$]") as "$".
  iPoseProof ("H2" with "[$]") as "$".
Qed.

Lemma wand_sepcon:
 forall {BI : bi} (P Q : BI),
   (P -∗ Q ∗ P) ∗ P ⊣⊢ Q ∗ P.
Proof.
  intros; iSplit.
  - by iIntros "(H & ?)"; iApply "H".
  - iIntros "($ & ?)"; iSplitL ""; auto.
Qed.

Lemma wand_sepcon':
 forall {BI : bi} (P Q : BI),
   P ∗ (P -∗ Q ∗ P) ⊣⊢ P ∗ Q.
Proof.
  intros; rewrite comm wand_sepcon comm //.
Qed.

Lemma replace_nth_overflow: forall {A} n l (v : A), (~n < length l)%nat -> replace_nth n l v = l.
Proof.
  induction n; destruct l; simpl; auto; intros.
  - lia.
  - rewrite IHn //; lia.
Qed.

Lemma extract_nth_exists_in_SEP:
  forall n P Q (R: list mpred)
              {A} (S: A -> mpred),
   nth n R emp = (∃ x, S x) ->
   PROPx P (LOCALx Q (SEPx R)) ⊣⊢
   ∃ x, PROPx P (LOCALx Q (SEPx (replace_nth n R (S x)))).
Proof.
  intros.
  destruct (lt_dec n (length R)).
  - eapply nth_error_nth in l; setoid_rewrite H in l.
    rewrite SEP_nth_isolate // PROP_LOCAL_SEP_cons embed_exist bi.sep_exist_r.
    f_equiv; intros ?.
    rewrite -PROP_LOCAL_SEP_cons -SEP_replace_nth_isolate //.
  - rewrite nth_overflow in H; last lia.
    iSplit.
    + iIntros "H"; iAssert ⌜∃ x : A, True⌝ as %(x & ?).
      { rewrite -(bi.emp_sep (PROPx _ _)) -embed_emp H embed_exist.
        iDestruct "H" as "((% & ?) & ?)"; auto. }
      iExists x; rewrite replace_nth_overflow //.
    + iIntros "(% & ?)"; rewrite replace_nth_overflow //.
Qed.

Lemma derives_extract_PROP' :
  forall {A} (P1: Prop) P QR S,
     (P1 -> PROPx P QR ⊢ S) ->
     @PROPx A Σ (P1::P) QR ⊢ S.
Proof.
  intros.
  rewrite -(bi.True_and (PROPx _ _)).
  apply derives_extract_PROP; intros; rewrite bi.and_elim_r; auto.
Qed.

End mpred.

#[export] Hint Resolve func_ptr_isptr: saturate_local.
#[export] Hint Rewrite @lift0_unfold @lift1_unfold @lift2_unfold @lift3_unfold @lift4_unfold : norm2.
#[export] Hint Rewrite @lift0_unfoldC @lift1_unfoldC @lift2_unfoldC @lift3_unfoldC @lift4_unfoldC : norm2.
#[export] Hint Rewrite @alift0_unfold @alift1_unfold @alift2_unfold @alift3_unfold @alift4_unfold : norm2.
#[export] Hint Rewrite @subst_lift0' : subst.
#[export] Hint Rewrite @subst_lift0 @subst_lift0C : subst.
#[export] Hint Rewrite @subst_lift1 @subst_lift1C  : subst.
#[export] Hint Rewrite @subst_lift2 @subst_lift2C : subst.
#[export] Hint Rewrite @subst_lift3 @subst_lift3C : subst.
#[export] Hint Rewrite @subst_lift4 @subst_lift4C : subst.

#[export] Hint Rewrite eval_id_same : norm.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.
#[export] Hint Rewrite simpl_get_result1: norm.
#[export] Hint Rewrite retval_get_result1 : norm.
#[export] Hint Rewrite retval_lemma1 : norm.
#[export] Hint Rewrite retval_make_args: norm2.
(*#[export] Hint Rewrite andp_makeargs: norm2.
#[export] Hint Rewrite local_makeargs: norm2.
#[export] Hint Rewrite liftx_local_retval : norm2.*)
#[export] Hint Rewrite bool_val_notbool_ptr using apply Coq.Init.Logic.I : norm.
#[export] Hint Rewrite typed_true_isptr using apply Coq.Init.Logic.I : norm.

Ltac super_unfold_lift_in H :=
   cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota in H.

Ltac super_unfold_lift' :=
  cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota.

Tactic Notation "name" ident(s) constr(id) :=
    idtac "Warning: the 'name' tactic no loger does anything useful, and will be removed in future versions of VST".

Definition abbreviate {A:Type} (x:A) := x.
Arguments abbreviate {A} {x}.

Ltac clear_Delta :=
match goal with
| Delta := @abbreviate tycontext ?G |- _ =>
   try match goal with |- context [ret_type Delta] =>
      let x := constr:(ret_type G) in let x := eval hnf in x
       in change (ret_type Delta) with x in *
   end;
   try clear Delta
| _ => idtac
end;
match goal with
 |  DS := @abbreviate (Maps.PTree.t funspec) _  |- _ =>
   first [clear DS | clearbody DS]
 | |- _ => idtac
 end.

Ltac clear_Delta_specs :=
 lazymatch goal with
 |  DS := @abbreviate (Maps.PTree.t funspec) _  |- _ => clearbody DS
 | |- _ => idtac
 end.

#[export] Hint Rewrite sem_cast_pointer2' using (try apply Coq.Init.Logic.I; try assumption; reflexivity) : norm.
#[export] Hint Rewrite is_pointer_or_null_force_int_ptr using assumption : norm1.
#[export] Hint Rewrite is_pointer_force_int_ptr using assumption : norm1.
#[export] Hint Rewrite is_pointer_or_null_match using assumption : norm1.
#[export] Hint Rewrite is_pointer_force_int_ptr2 using assumption : norm1.
#[export] Hint Rewrite is_pointer_or_null_force_int_ptr2 using assumption : norm1.
#[export] Hint Rewrite isptr_match : norm1.
#[export] Hint Rewrite eval_cast_neutral_tc_val using solve [eauto] : norm.
#[export] Hint Rewrite eval_cast_neutral_is_pointer_or_null using assumption : norm.
#[export] Hint Rewrite is_pointer_or_null_eval_cast_neutral : norm.
#[export] Hint Rewrite eval_cast_neutral_isptr using assumption : norm.
(*#[export] Hint Rewrite simpl_and_get_result1 : norm2.*)

Arguments ret_type {_ _} !Delta /.

Arguments Datatypes.id {A} x / .

#[export] Hint Rewrite @raise_sepcon : norm1.
#[export] Hint Rewrite @lift_lift_retval: norm2.
#[export] Hint Rewrite lift_lift_x : norm2.
#[export] Hint Rewrite @lift0_exp : norm2.
#[export] Hint Rewrite @lift0C_exp : norm2.
#[export] Hint Rewrite @lift0C_sepcon : norm.
#[export] Hint Rewrite @lift0C_andp : norm.
#[export] Hint Rewrite @lift0C_exp : norm.
#[export] Hint Rewrite @lift0C_later : norm.
#[export] Hint Rewrite @lift0C_prop : norm.

#[export] Hint Rewrite
    @lift1_lift1_retval
    @lift0_exp
    @lift0_sepcon
    @lift0_prop
    @lift0_later
    : norm2.

Lemma derives_refl {BI : bi} (P : BI) : P ⊢ P.
Proof. done. Qed.

#[export] Hint Rewrite @fst_unfold @snd_unfold : norm.
#[export] Hint Rewrite @local_andp_prop @local_andp_prop1 : norm2.
#[export] Hint Rewrite @local_sepcon_assoc1 @local_sepcon_assoc2 : norm2.
#[export] Hint Resolve andp_later_derives sepcon_later_derives bi.sep_mono
              bi.and_mono bi.impl_mono bi.later_intro derives_refl: derives.
#[export] Hint Rewrite @prop_true_andp1 using solve [auto 3 with typeclass_instances]: norm1.
#[export] Hint Rewrite @prop_true_andp1 using assumption : norm.

Ltac strip1_later P cP :=
 lazymatch P with
 | do_canon ?L ?R =>
     let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(do_canon L' R') in cP P')
           in  strip1_later R cR)
      in strip1_later L cL
 | PROPx ?A ?QR =>
           let cQR := (fun QR' => let P' := constr:(PROPx A QR') in cP P')
            in strip1_later QR cQR
 | LOCALx ?Q ?R =>
           let cR := (fun R' => let P' := constr:(LOCALx Q R') in cP P')
            in strip1_later R cR
 | @SEPx environ ?R =>
    let cR := fun R' => (let P' := constr:(@SEPx environ _ R') in cP P') in
     strip1_later R cR
 | ?L :: ?R =>
      let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(L'::R') in cP P') in
          strip1_later R cR)
       in strip1_later L cL
 | ?L ∧ ?R =>
      let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(L'∧R') in cP P') in
          strip1_later R cR)
       in strip1_later L cL
 | ?L ∗ ?R =>
      let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(L' ∗ R') in cP P') in
          strip1_later R cR)
       in strip1_later L cL
 | ▷ ?L => cP L
 | _ => cP P
end.

Declare Scope funspec_scope.
Delimit Scope funspec_scope with funspec.
Global Open Scope funspec_scope.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Definition NDsemax_external `{!heapGS Σ} {Hspec: OracleKind} `{!externalGS OK_ty Σ} E (ef: external_function)
  (A: Type) (P:A -> argsassert) (Q: A -> assert): Prop :=
  ⊢ semax_external E ef (ConstType A) (λne (x : leibnizO A), P x : _ -d> mpred) (λne (x : leibnizO A), Q x : _ -d> mpred).

Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default tx (fun x => P%argsassert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH' x : tx 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default tx (fun x => P%argsassert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%argsassert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%argsassert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%argsassert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%argsassert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0, x21 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0, x21 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 , x22 : t22 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21*t22)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0, x21 at level 0, x22 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 , x22 : t22 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21*t22)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0, x21 at level 0, x22 at level 0,
              P at level 100, Q at level 100) : funspec_scope.

(* Notations for dependent funspecs *)

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) cc_default A
  (λne (x: t1*t2),
     match x with (x1,x2) => P%argsassert end)
  (λne (x: t1*t2),
     match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2),
     match x with (x1,x2) => P%argsassert end)
  (λne (x: t1*t2),
     match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3),
     match x with (x1,x2,x3) => P%argsassert end)
  (λne (x: t1*t2*t3),
     match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) cc_default A
  (λne (x: t1*t2*t3),
     match x with (x1,x2,x3) => P%argsassert end)
  (λne (x: t1*t2*t3),
     match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3*t4),
     match x with (x1,x2,x3,x4) => P%argsassert end)
  (λne (x: t1*t2*t3*t4),
     match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3*t4*t5),
     match x with (x1,x2,x3,x4,x5) => P%argsassert end)
  (λne (x: t1*t2*t3*t4*t5),
     match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3*t4*t5*t6),
     match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
  (λne (x: t1*t2*t3*t4*t5*t6),
     match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3*t4*t5*t6*t7),
     match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
  (λne (x: t1*t2*t3*t4*t5*t6*t7),
     match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3*t4*t5*t6*t7*t8),
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
  (λne (x: t1*t2*t3*t4*t5*t6*t7*t8),
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (λne (x: t1*t2*t3*t4*t5*t6*t7*t8*t9),
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
  (λne (x: t1*t2*t3*t4*t5*t6*t7*t8*t9),
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
  (fun (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100).

Notation LAMBDAx gs vals X := (PARAMSx vals (GLOBALSx gs X)) (only parsing).

Ltac splittablex_tac A :=
 match A with
 | _ <= _ < _ => fail 1
 | _ < _ <= _ => fail 1
 | _ <= _ <= _ => fail 1
 | _ < _ < _ => fail 1
 | _ <-> _ => fail 1
 | _ /\ _ => apply Logic.I
 end.

#[export] Hint Rewrite @and_assoc_splittablex using
    match goal with |- splittablex ?A => splittablex_tac A end : normalize.
#[export] Hint Rewrite @and_assoc_splittablex using
    match goal with |- splittablex ?A => splittablex_tac A end : gather_prop.
#[export] Hint Rewrite @prop_and1 using solve [auto 3 with typeclass_instances] : norm2.
#[export] Hint Rewrite @subst_make_args' using (solve[reflexivity]) : subst.
#[export] Hint Rewrite @map_cons : norm.
#[export] Hint Rewrite @map_cons : subst.
#[export] Hint Rewrite @map_nil : norm.
#[export] Hint Rewrite @map_nil : subst.
#[export] Hint Rewrite @subst_stackframe_of : subst.
#[export] Hint Rewrite @wand_sepcon @wand_sepcon' : norm.

Ltac hoist_later_left :=
   match goal with
  | |- (?P ⊢ _) =>
        let cP := (fun P' =>
                   trans (▷P');
                    [ solve [ auto 50 with derives ] | ])
     in strip1_later P cP
  end.

(* Willam proposed that this versions of assert_PROP replace the ones in canon.v. *)
Tactic Notation "assert_PROP" constr(A) :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ | intro ].

Tactic Notation "assert_PROP" constr(A) "by" tactic1(t) :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ now t | intro ].

Tactic Notation "assert_PROP" constr(A) "as" simple_intropattern(H)  :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ | intro H ].

Tactic Notation "assert_PROP" constr(A) "as" simple_intropattern(H) "by" tactic1(t) :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ now t | intro H ].
Ltac hoist_later_in_pre :=
     match goal with |- semax _ _ ?P _ _ =>
       match P with
       | context[bi_later] =>
            let cP := (fun P' => apply semax_pre0 with (▷ P'); [solve [auto 50 with derives] | ])
             in strip1_later P cP
       | _ => apply semax_later_trivial
       end
     end.

Ltac simpl_tc_expr :=
    match goal with |- context [tc_expr ?A ?B] =>
        change (tc_expr A B) with (denote_tc_assert (typecheck_expr A B));
     (* These uses of 'simpl' are not too dangerous, for two reasons:
          (1) simpl_tc_expr is not used by any parts of Floyd except explicitly deprecated parts
          (2) the simpl is unlikely to blow up, because the arguments are just
                  clightgen-produced ASTs *)
        simpl typecheck_expr; simpl denote_tc_assert
    end.

Ltac make_sequential :=
  match goal with
  | |- @semax _ _ _ _ _ _ _ _ _ (normal_ret_assert _) => idtac
  | |- _ => apply sequential
  end.

Ltac intro_if_new :=
 repeat match goal with
  | |- ?A -> _ => ((assert A by auto; fail 1) || fail 1) || intros _
  | |- (_ <-> _) -> _ =>
         intro
  | |- (?A /\ ?B) -> ?C =>
         apply (@and_ind A B C)
  | |- isptr (force_ptr ?P) -> ?Q =>
         apply (isptr_force_ptr'' P Q)
  | |- isptr (offset_val ?i ?P) -> ?Q =>
         apply (isptr_offset_val'' i P Q)
  | H: is_pointer_or_null ?P |- isptr ?P -> _ =>
         clear H
  | |- ?x = ?y -> _ =>
          let H := fresh in intro H;
                     first [subst x | subst y
                             | is_var x; rewrite H
                             | is_var y; rewrite <- H
                             | solve [discriminate H]
                             | idtac]
  | |- isptr ?x -> _ =>
          let H := fresh "P" x in intro H
  | |- is_pointer_or_null ?x =>
          let H := fresh "PN" x in intro H
  | |- typed_false _ (bool2val _) -> _ =>
          simple apply typed_false_of_bool'
  | |- typed_true _ (bool2val _) -> _ =>
          simple apply typed_true_of_bool'
  | |- ptr_eq _ _ -> _ =>
          apply ptr_eq_e'
  | |- _ -> _ =>
          intro
  end.

Ltac already_saturated :=
(match goal with |- ?P ⊢ ?Q =>
    let H := fresh in
     assert (H: P ⊢ Q) by auto with nocore saturate_local;
     cbv beta in H;
     match type of H with _ ⊢ ⌜?Q'⌝ =>
     assert (Q') by (repeat simple apply conj; auto);
     fail 3
     end
end || auto with nocore saturate_local)
 || simple apply TT_right.

Ltac check_mpreds2 R :=
 lazymatch R with
 | bi_sep ?a ?b => check_mpreds2 a; check_mpreds2 b
 | _ => match type of R with ?t =>
                          first [unify t (@iProp _)
                                 | fail 4 "The conjunct" R "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end
 | nil => idtac
 end.

Ltac saturate_local :=
(* match goal with |- ?R ⊢ _ => check_mpreds2 R end; Do we need this? *)
 eapply saturate_aux21x;
 [repeat simple apply saturate_aux20;
   (* use already_saturated if want to be fancy,
         otherwise the next lines *)
    auto with nocore saturate_local;
     (*simple*) apply TT_right
 | (*simple*) apply bi.pure_elim_l;
   match goal with |- _ -> ?A =>
       let P := fresh "P" in set (P := A);
       fancy_intros true;
       subst P
      end
 ].

(*********************************************************)

Ltac prop_right_cautious :=
 try solve [simple apply bi.pure_intro; auto].

Ltac subst_any :=
 repeat match goal with
  | H: ?x = ?y |- _ => first [ subst x | subst y ]
 end.
Ltac solve_mod_eq :=
  unfold Int.add, Int.mul;
  repeat rewrite Int.unsigned_repr_eq;
  repeat
  (repeat rewrite Zmod_mod;
  repeat rewrite Zmult_mod_idemp_l;
  repeat rewrite Zmult_mod_idemp_r;
  repeat rewrite Zplus_mod_idemp_l;
  repeat rewrite Zplus_mod_idemp_r).

Ltac extract_exists_in_SEP' PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(@bi_exist _ ?A ?S) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (@extract_nth_exists_in_SEP n' P Q R A S (eq_refl _));
      unfold replace_nth at 1;
      rewrite ?bi.and_exist_l
   end
 end.

Ltac extract_exists_from_SEP :=
lazymatch goal with
  | |- semax _ _ ?Pre _ _ =>
    extract_exists_in_SEP' Pre; apply extract_exists_pre
  | |- ENTAIL _, ?Pre ⊢ ?Post =>
     let P := fresh "POST" in set (P := Post);
    extract_exists_in_SEP' Pre; subst P; apply bi.exist_elim
  | |- ?Pre ⊢ ?Post => (* this case is obsolete, should probably be deleted *)
     let P := fresh "POST" in set (P := Post);
    extract_exists_in_SEP' Pre; subst P; apply bi.exist_elim
end.

Ltac move_from_SEP' PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(⌜?P1⌝ ∧ ?S) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (extract_prop_in_SEP n' P1 S P Q R (eq_refl _));
      unfold replace_nth at 1
   end
 end.

Ltac test_for_Intro_prop R :=
 lazymatch R with
 | nil => fail
 | ?A :: ?B => first [test_for_Intro_prop A | test_for_Intro_prop B]
 | @bi_exist _ _ _  => fail
 | ⌜_⌝ => idtac
 | ?A ∧ ?B => first [test_for_Intro_prop A | test_for_Intro_prop B]
 | ?A ∗ ?B =>  first [test_for_Intro_prop A | test_for_Intro_prop B]
 end.

Ltac Intro_prop' :=
lazymatch goal with
 | |- semax _ _ ?PQR _ _ =>
     first [ move_from_SEP' PQR;
              simple apply semax_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
            ]
 | |- ENTAIL _, ?PQR ⊢ _ =>
     first [ move_from_SEP' PQR;
               simple apply derives_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
             ]
 | |- ?PQR ⊢ _ =>
     first [ match PQR with ⌜_⌝ ∧ _ => apply bi.pure_elim_l; fancy_intros false end
            | move_from_SEP' PQR;
               simple apply derives_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
             ]
end.

Ltac Intro_prop :=
(*  Intro_prop is written this complicated way to avoid doing
    [autorewrite with gather_prop_core] which is expensive, and
   to avoid [autorewrite with gather_prop] which is even more expensive. *)
lazymatch goal with
 | |- semax _ _ ?PQR _ _ => tryif is_evar PQR then fail else idtac
 | |- ENTAIL _, ?PQR ⊢ _ => tryif is_evar PQR then fail else idtac
 | |- ?PQR ⊢ _ => tryif is_evar PQR then fail else idtac
end;
first
 [ simple apply semax_extract_PROP; fancy_intros false
 | simple apply derives_extract_PROP; fancy_intros false
 |
lazymatch goal with
 | |- ENTAIL _, @bi_exist _ _ _ ⊢ _ =>  fail
 | |- semax _ _ (@bi_exist _) _ _ => fail
 | |- ENTAIL _, PROPx nil (LOCALx _ (SEPx ?R)) ⊢ _ => test_for_Intro_prop R
 | |- semax _ _ PROPx nil (LOCALx _ (SEPx ?R)) _ _ => test_for_Intro_prop R
 | |- _ => idtac
 end;
 tryif Intro_prop' then idtac
 else tryif progress autorewrite with gather_prop_core
    then first [Intro_prop' | progress gather_prop; Intro_prop']
    else (progress gather_prop; Intro_prop')
 ].

(* Would this be faster with pattern matching? *)
Ltac Intro'' a :=
  tryif apply extract_exists_pre then intro a
  else tryif apply bi.exist_elim then intro a
  else tryif extract_exists_from_SEP then intro a
  else tryif rewrite bi.and_exist_l then Intro'' a
  else tryif rewrite bi.and_exist_r then Intro'' a
  else tryif rewrite bi.sep_exist_l then Intro'' a
  else tryif rewrite bi.sep_exist_r then Intro'' a
  else fail.

Ltac Intro a :=
  repeat Intro_prop;
  lazymatch goal with
  | |- ?A ⊢ ?B =>
     let z := fresh "z" in pose (z:=B); change (A⊢z); Intro'' a; subst z
  | |- semax _ _ _ _ _ =>
     Intro'' a
  end.

Tactic Notation "Intro" "?" :=
  lazymatch goal with
  | |- semax _ _ ?x _ _ =>
    lazymatch x with context [∃ ex1 : _, _] =>
      let e1 := fresh ex1 in Intro e1
    end
  | |- context [?Pre ⊢ _] =>
    lazymatch Pre with context [∃ ex1 : _, _] =>
      let e1 := fresh ex1 in Intro e1
    end
  end.

Ltac finish_Intros :=
repeat Intro_prop;
(* Do this next part for backwards compatibility *)
lazymatch goal with
 | |- ?A _ => let x := fresh "x" in set(x:=A);
        gather_prop; subst x
end.

Tactic Notation "Intros" := finish_Intros.

Tactic Notation "Intros" "*" :=
  repeat Intro ?; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0) :=
 Intro x0; finish_Intros.

Tactic Notation "Intros" "?" :=
 Intro ?; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) :=
 Intro x0; Intro x1; finish_Intros.

Tactic Notation "Intros" "?" "?" :=
 Intro ?; Intro ?; finish_Intros.

Tactic Notation "Intros" "?" simple_intropattern(x0) :=
 Intro ?; Intro x0; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0) "?" :=
 Intro x0; Intro ?; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2) :=
 Intro x0; Intro x1; Intro x2; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) :=
 Intro x0; Intro x1; Intro x2; Intro x3; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10)
 simple_intropattern(x11) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; Intro x11; finish_Intros.


Ltac extract_exists_from_SEP_right :=
match goal with
  | |- ?Pre ⊢ ?Post =>
     let P := fresh "PRE" in set (P := Pre);
    extract_exists_in_SEP' Post; subst P
end.

Ltac Exists'' a :=
  first [rewrite -(bi.exist_intro a)
         | rewrite bi.and_exist_l; Exists'' a
         | rewrite bi.and_exist_r; Exists'' a
         | rewrite bi.sep_exist_l; Exists'' a
         | rewrite bi.sep_exist_r; Exists'' a
         | extract_exists_from_SEP_right; rewrite -(bi.exist_intro a)
         ].

Ltac Exists' a :=
  match goal with |- ?A ⊢ ?B =>
     let z := fresh "z" in pose (z:=A); change (z⊢B); Exists'' a; subst z
  end.

Tactic Notation "Exists" constr(x0) :=
 Exists' x0.

Tactic Notation "Exists" "?" :=
 lazymatch goal with
 | |- _ ⊢ ?Post =>
  lazymatch Post with context [∃ ex : _, _] => Exists' ex end
 end.

Tactic Notation "Exists" constr(x0) constr(x1) :=
 Exists' x0; Exists' x1.

Tactic Notation "Exists" "?" "?" :=
 do 2 Exists ?.

Tactic Notation "Exists" "?" constr(x0) :=
 Exists ?; Exists' x0.

Tactic Notation "Exists" constr(x0) "?" :=
 Exists' x0; Exists ?.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) :=
 Exists' x0; Exists' x1; Exists' x2.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) constr(x12) :=
 Exists' x0; Exists' x1; Exists x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11; Exists' x12.

(* EExists *)
Ltac my_evar name T cb :=
  let x := fresh name
  in
  evar (x : T);
    let x' := eval unfold x in x
    in
    clear x; cb x'.

Ltac tuple_evar name T cb :=
  lazymatch T with
  | prod ?A ?B => tuple_evar name A
    ltac: (fun xA =>
      tuple_evar name B ltac: (fun xB =>
        cb (xA, xB)))
  | _ => my_evar name T cb
  end; idtac.

Ltac EExists'' :=
  let EExists_core :=
    match goal with [ |- _ ⊢ ∃ x:?T, _ ] =>
      tuple_evar x T ltac: (fun x => rewrite -(bi.exist_intro x))
    end; idtac
  in
  first [ EExists_core
         | rewrite bi.and_exist_l; EExists''
         | rewrite bi.and_exist_r; EExists''
         | rewrite bi.sep_exist_l; EExists''
         | rewrite bi.sep_exist_r; EExists''
         | extract_exists_from_SEP_right; EExists_core
         ].

Ltac EExists' :=
  match goal with |- ?A ⊢ ?B =>
     let z := fresh "z" in pose (z:=A); change (z⊢B); EExists''; unfold z at 1; clear z
  end.

Ltac EExists := EExists'.

Ltac EExists_alt :=
  let T := fresh "T"
  in
  let x := fresh "x"
  in
  evar (T:Type); evar (x:T); subst T; Exists x; subst x.

Tactic Notation "freeze1" uconstr(a) :=
    let x := fresh "x" in set (x:=a);
    let fr := fresh "freeze" in pose (fr := @abbreviate mpred x);
    change (cons x) with (cons fr); subst x.
