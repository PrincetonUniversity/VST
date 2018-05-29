Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.local2ptree_denote.

Local Open Scope logic.

Definition eval_vardesc (ty: type) (vd: option vardesc) : option val :=
                    match  vd with
                    | Some (vardesc_local_global ty' v _) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | Some (vardesc_local ty' v) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | Some (vardesc_visible_global v) =>
                          Some v
                    | Some (vardesc_shadowed_global _) =>
                          None
                    | None => None
                    end.

Definition eval_lvardesc (ty: type) (vd: option vardesc) : option val :=
                    match  vd with
                    | Some (vardesc_local_global ty' v _)
                    | Some (vardesc_local ty' v) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | _ => None
                    end.

Fixpoint msubst_eval_expr {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (e: Clight.expr) : option val :=
  match e with
  | Econst_int i ty => Some (Vint i)
  | Econst_long i ty => Some (Vlong i)
  | Econst_float f ty => Some (Vfloat f)
  | Econst_single f ty => Some (Vsingle f)
  | Etempvar id ty => PTree.get id T1
  | Eaddrof a ty => msubst_eval_lvalue T1 T2 a
  | Eunop op a ty => option_map (eval_unop op (typeof a))
                                        (msubst_eval_expr T1 T2 a)
  | Ebinop op a1 a2 ty =>
      match (msubst_eval_expr T1 T2 a1), (msubst_eval_expr T1 T2 a2) with
      | Some v1, Some v2 => Some (eval_binop op (typeof a1) (typeof a2) v1 v2)
      | _, _ => None
      end
  | Ecast a ty => option_map (eval_cast (typeof a) ty) (msubst_eval_expr T1 T2 a)
  | Evar id ty => eval_vardesc ty (PTree.get id T2)

  | Ederef a ty => msubst_eval_expr T1 T2 a
  | Efield a i ty => option_map (eval_field (typeof a) i) (msubst_eval_lvalue T1 T2 a)
  | Esizeof t _ => Some (Vptrofs (Ptrofs.repr (sizeof t)))
  | Ealignof t _ => Some (Vptrofs (Ptrofs.repr (alignof t)))
  end
  with msubst_eval_lvalue {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (e: Clight.expr) : option val :=
  match e with
  | Evar id ty => eval_vardesc ty (PTree.get id T2)
  | Ederef a ty => msubst_eval_expr T1 T2 a
  | Efield a i ty => option_map (eval_field (typeof a) i)
                              (msubst_eval_lvalue T1 T2 a)
  | _  => Some Vundef
  end.

Definition msubst_eval_LR {cs: compspecs} T1 T2 e (lr: LLRR) :=
  match lr with
  | LLLL => msubst_eval_lvalue T1 T2 e
  | RRRR => msubst_eval_expr T1 T2 e
  end.

Definition msubst_eval_lvar {cs: compspecs} T2 i t :=
  eval_lvardesc t (PTree.get i T2).

Lemma msubst_eval_expr_eq_aux:
  forall {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) e rho v,
    (forall i v, T1 ! i = Some v -> eval_id i rho = v) ->
    (forall i t v,
     eval_vardesc t T2 ! i = Some v -> eval_var i t rho = v) ->
    msubst_eval_expr T1 T2 e = Some v ->
    eval_expr e rho = v
with msubst_eval_lvalue_eq_aux:
  forall {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) e rho v,
    (forall i v, T1 ! i = Some v -> eval_id i rho = v) ->
    (forall i t v,
     eval_vardesc t T2 ! i = Some v -> eval_var i t rho = v) ->
    msubst_eval_lvalue T1 T2 e = Some v ->
    eval_lvalue e rho = v.
Proof.
  + clear msubst_eval_expr_eq_aux.
    induction e; intros; simpl in H1 |- *; try solve [inversion H1; auto].
    - erewrite msubst_eval_lvalue_eq_aux; eauto.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e1) eqn:?; [| inversion H1].
      destruct (msubst_eval_expr T1 T2 e2) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe1 with (v := v0) by auto.
      rewrite IHe2 with (v := v1) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_lvalue T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      erewrite msubst_eval_lvalue_eq_aux by eauto.
      reflexivity.
  + clear msubst_eval_lvalue_eq_aux.
    induction e; intros; simpl in H1 |- *; try solve [inversion H1; auto].
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      erewrite msubst_eval_expr_eq_aux by eauto;
      auto.
    - unfold_lift; simpl.
      destruct (msubst_eval_lvalue T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
Qed.

Lemma msubst_eval_eq_aux {cs: compspecs}: forall T1 T2 Q rho,
  fold_right `(and) `(True) (map locald_denote (LocalD T1 T2 Q)) rho ->
  (forall i v, T1 ! i = Some v -> eval_id i rho = v) /\
  (forall i t v, eval_vardesc t (T2 ! i) = Some v ->
      eval_var i t rho = v).
Proof.
  intros; split; intros.
  + intros.
    assert (In (locald_denote (temp i v)) (map locald_denote (LocalD T1 T2 Q))).
      apply  in_map.
      apply LocalD_sound.
      left.
      eauto.
    pose proof local_ext _ _ _ H1 H.
    unfold_lift in H2.
    auto.
  + intros.
      unfold eval_vardesc in H0.
      destruct (T2 ! i) as [ [?|?|?|?] | ] eqn:HT; simpl in *.
    -destruct (eqb_type t t0) eqn:?; inv H0.
      apply eqb_type_true in Heqb. subst t0.
      assert (In (locald_denote (lvar i t v))  (map locald_denote (LocalD T1 T2 Q)))
        by ( apply  in_map; apply LocalD_sound; eauto 50).
      assert (H3 := local_ext _ _ _ H0 H). clear - H3.
      unfold eval_var in *. hnf in H3.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      destruct H3; subst. rewrite eqb_type_refl. auto.
     -destruct (eqb_type t t0) eqn:?; inv H0.
      apply eqb_type_true in Heqb. subst t0.
      assert (In (locald_denote (lvar i t v)) (map locald_denote (LocalD T1 T2 Q)))
        by (apply  in_map; apply LocalD_sound; eauto 50).
      assert (H3 := local_ext _ _ _ H0 H). clear - H3.
      unfold eval_var in *. hnf in H3.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      destruct H3; subst. rewrite eqb_type_refl. auto.
     - inv H0.
      assert (In (locald_denote (gvar i v)) (map locald_denote (LocalD T1 T2 Q)))
        by (apply  in_map; apply LocalD_sound; eauto 50).
      assert (H3 := local_ext _ _ _ H0 H). clear - H3.
      unfold eval_var in *. hnf in H3.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      destruct (Map.get (ge_of rho) i); try contradiction. auto.
     - inv H0.
     - inv H0.
Qed.

Lemma msubst_eval_lvar_eq_aux {cs: compspecs}: forall T1 T2 Q rho,
  fold_right `(and) `(True) (map locald_denote (LocalD T1 T2 Q)) rho ->
  (forall i t v, eval_lvardesc t (T2 ! i) = Some v ->
      eval_lvar i t rho = v).
Proof.
  intros.
  unfold eval_lvar.
  unfold eval_lvardesc in H0.
  destruct (T2 ! i) as [ [?|?|?|?] | ] eqn:?H; simpl in *.
  + destruct (eqb_type t t0) eqn:?H; inv H0.
    apply eqb_type_true in H2; subst t0.
    assert (In (locald_denote (lvar i t v))  (map locald_denote (LocalD T1 T2 Q)))
      by ( apply  in_map; apply LocalD_sound; eauto 50).
    assert (H3 := local_ext _ _ _ H0 H). clear - H3.
    hnf in H3.
    destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
    destruct H3; subst. rewrite eqb_type_refl. auto.
  + destruct (eqb_type t t0) eqn:?H; inv H0.
    apply eqb_type_true in H2; subst t0.
    assert (In (locald_denote (lvar i t v))  (map locald_denote (LocalD T1 T2 Q)))
      by ( apply  in_map; apply LocalD_sound; eauto 50).
    assert (H3 := local_ext _ _ _ H0 H). clear - H3.
    hnf in H3.
    destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
    destruct H3; subst. rewrite eqb_type_refl. auto.
  + inv H0.
  + inv H0.
  + inv H0.
Qed.

Lemma msubst_eval_expr_eq: forall {cs: compspecs} P T1 T2 Q R e v,
  msubst_eval_expr T1 T2 e = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_expr e)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
      autorewrite with subst norm1 norm2; normalize.
  destruct (msubst_eval_eq_aux _ _ _ _ H0).
  apply eq_sym, (msubst_eval_expr_eq_aux T1 T2); auto.
Qed.

Lemma msubst_eval_lvalue_eq: forall P {cs: compspecs} T1 T2 Q R e v,
  msubst_eval_lvalue T1 T2 e = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_lvalue e)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
      autorewrite with subst norm1 norm2; normalize.
  destruct (msubst_eval_eq_aux _ _ _ _ H0).
  apply eq_sym, (msubst_eval_lvalue_eq_aux T1 T2); auto.
Qed.

Lemma msubst_eval_LR_eq: forall {cs: compspecs} P T1 T2 Q R e v lr,
  msubst_eval_LR T1 T2 e lr = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_LR e lr)).
Proof.
  intros.
  destruct lr.
  + apply msubst_eval_lvalue_eq; auto.
  + apply msubst_eval_expr_eq; auto.
Qed.

Lemma msubst_eval_exprlist_eq:
  forall P {cs: compspecs} T1 T2 Q R tys el vl,
  force_list
           (map (msubst_eval_expr T1 T2)
              (explicit_cast_exprlist tys el)) = Some vl ->
 PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
   local (`(eq vl) (eval_exprlist tys el)).
Proof.
intros.
revert tys vl H; induction el; destruct tys, vl; intros;
  try solve [inv H];
  try solve [go_lowerx;  apply prop_right; reflexivity].
 simpl map in H.
 unfold force_list in H; fold (@force_list val) in H.
 destruct (msubst_eval_expr T1 T2 a) eqn:?.
 simpl in H.
 destruct (force_list
        (map (msubst_eval_expr T1 T2) (explicit_cast_exprlist tys el))); inv H.
 simpl in H. inv H.
 simpl in H.
 destruct (option_map (force_val1 (sem_cast (typeof a) t))
        (msubst_eval_expr T1 T2 a)) eqn:?; inv H.
  destruct ( force_list
         (map (msubst_eval_expr T1 T2) (explicit_cast_exprlist tys el))) eqn:?; inv H1.
  specialize (IHel _ _ Heqo0).
  simpl eval_exprlist.
  destruct (msubst_eval_expr T1 T2 a) eqn:?; inv Heqo.
  apply msubst_eval_expr_eq with (P0:=P)(Q0:=Q)(R0:=R) in Heqo1.
  apply derives_trans with (local (`(eq v0) (eval_expr a)) && local (`(eq vl) (eval_exprlist tys el))).
  apply andp_right; auto.
  go_lowerx. unfold_lift. intros. apply prop_right.
  rewrite <- H. rewrite <- H0.
 auto.
Qed.

Lemma msubst_eval_lvar_eq: forall {cs: compspecs} P T1 T2 Q R i t v,
  msubst_eval_lvar T2 i t = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_lvar i t)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
      autorewrite with subst norm1 norm2; normalize.
  pose proof (msubst_eval_lvar_eq_aux _ _ _ _ H0).
  apply eq_sym.
  apply H1; auto.
Qed.
  
Ltac solve_msubst_eval_lvalue :=
  simpl;
  cbv beta iota zeta delta [force_val2 force_val1];
  rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto;
  reflexivity.

Ltac solve_msubst_eval_expr :=
  simpl;
  cbv beta iota zeta delta [force_val2 force_val1];
  rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto;
  reflexivity.

Ltac solve_msubst_eval_LR :=
  unfold msubst_eval_LR;
  simpl;
  cbv beta iota zeta delta [force_val2 force_val1];
  rewrite ?isptr_force_ptr, <- ?offset_val_force_ptr by auto;
  reflexivity.

Ltac solve_msubst_eval_lvar :=
  unfold msubst_eval_lvar; reflexivity.

(**********************************************************)
(* Continuation *)
(*
Require Import VST.veric.xexpr_rel.


Inductive l_cont : Type :=
  | LC_deref : r_cont -> l_cont
  | LC_field : l_cont -> type -> ident -> l_cont
with r_cont : Type :=
  | RC_addrof : l_cont -> r_cont
  | RC_unop : unary_operation -> r_cont -> type -> r_cont
  | RC_binop_l : binary_operation -> r_cont -> type -> r_value -> type -> r_cont
  | RC_binop_r : binary_operation -> val -> type -> r_cont -> type -> r_cont
  | RC_cast : r_cont -> type -> type -> r_cont
  | RC_byref: l_cont -> r_cont
  | RC_load: r_cont.


Definition sum_map {A B C D : Type} (f : A -> B) (g: C -> D) (x : A + C) :=
match x with
| inl y => inl (f y)
| inr z => inr (g z)
end.

Definition prod_left_map {A B C} (f: A -> B) (x: A * C) : B * C :=
  match x with
  | (x1, x2) => (f x1, x2)
  end.

Definition compute_cont_map {A B} (f: val -> val) (g: A -> B) : option (val + (A * (l_value * type))) -> option (val + (B * (l_value * type))) := option_map (sum_map f (prod_left_map g)).

Fixpoint compute_r_cont {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (e: r_value) : option (val + (r_cont * (l_value * type))) :=
  match e with
  | R_const v => Some (inl v)
  | R_tempvar id => option_map inl (PTree.get id T1)
  | R_addrof a => compute_cont_map id RC_addrof (compute_l_cont T1 T2 a)
  | R_unop op a ta => compute_cont_map (eval_unop op ta) (fun c => RC_unop op c ta) (compute_r_cont T1 T2 a)
  | R_binop op a1 ta1 a2 ta2 =>
      match compute_r_cont T1 T2 a1 with
      | Some (inl v1) => compute_cont_map (eval_binop op ta1 ta2 v1) (fun c => RC_binop_r op v1 ta1 c ta2) (compute_r_cont T1 T2 a2)
      | Some (inr (c, e_cont)) => Some (inr (RC_binop_l op c ta1 a2 ta2, e_cont))
      | None => None
      end
  | R_cast a ta ty => compute_cont_map (eval_cast ta ty) (fun c => RC_cast c ta ty) (compute_r_cont T1 T2 a)
  | R_byref a => compute_cont_map id RC_byref (compute_l_cont T1 T2 a)
  | R_load a ty => Some (inr (RC_load, (a, ty)))
  | R_ilegal _ => None
  end
with compute_l_cont {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (e: l_value) : option (val + (l_cont * (l_value * type))) :=
  match e with
  | L_var id ty => option_map inl (eval_vardesc ty (PTree.get id T2))
  | L_deref a => compute_cont_map force_ptr LC_deref (compute_r_cont T1 T2 a)
  | L_field a ta i => compute_cont_map (eval_field ta i) (fun c => LC_field c ta i) (compute_l_cont T1 T2 a)
  | L_ilegal _ => None
  end.

Fixpoint fill_r_cont (e: r_cont) (v: val): r_value :=
  match e with
  | RC_addrof a => R_addrof (fill_l_cont a v)
  | RC_unop op a ta => R_unop op (fill_r_cont a v) ta
  | RC_binop_l op a1 ta1 a2 ta2 => R_binop op (fill_r_cont a1 v) ta1 a2 ta2
  | RC_binop_r op v1 ta1 a2 ta2 => R_binop op (R_const v1) ta1 (fill_r_cont a2 v) ta2
  | RC_cast a ta ty => R_cast (fill_r_cont a v) ta ty
  | RC_byref a => R_byref (fill_l_cont a v)
  | RC_load => R_const v
  end
with fill_l_cont (e: l_cont) (v: val): l_value :=
  match e with
  | LC_deref a => L_deref (fill_r_cont a v)
  | LC_field a ta i => L_field (fill_l_cont a v) ta i
  end.


Lemma compute_LR_cont_sound: forall (cs: compspecs) (T1: PTree.t val) (T2: PTree.t vardesc) P Q R,
  (forall e v,
    compute_r_cont T1 T2 e = Some (inl v) ->
    PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- rel_r_value e v) /\
  (forall e v c e0 sh t p v0,
    compute_r_cont T1 T2 e = Some (inr (c, (e0, t))) ->
    PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- rel_l_value e0 p ->
    PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- `(mapsto sh t p v0) ->
    PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- rel_r_value (fill_r_cont c v0) v ->
    PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- rel_r_value e v). /\
*)
