Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import Coq.Classes.RelationClasses.
Require Import VST.floyd.sublist.
Require Import VST.floyd.stronger.

Require Import VST.floyd.stronger.
Section SINGLE_HOLE.

Context {cs: compspecs}.

Lemma gfield_dec: forall (gf0 gf1: gfield), {gf0 = gf1} + {gf0 <> gf1}.
Proof.
  intros.
  destruct gf0, gf1; try solve [right; congruence].
  + destruct (zeq i i0); [left | right]; congruence.
  + destruct (Pos.eq_dec i i0); [left | right]; congruence.
  + destruct (Pos.eq_dec i i0); [left | right]; congruence.
Defined.

Lemma rgfs_dec: forall rgfs0 rgfs1: list gfield, {rgfs0 = rgfs1} + {rgfs0 <> rgfs1}.
Proof.
  apply list_eq_dec.
  apply gfield_dec.
Defined.

Definition upd_gfield_reptype t gf (v: reptype t) (v0: reptype (gfield_type t gf)) : reptype t :=
  fold_reptype
  (match t, gf return (REPTYPE t -> reptype (gfield_type t gf) -> REPTYPE t)
  with
  | Tarray t0 n a, ArraySubsc i => upd_Znth i
(*zl_concat (zl_concat (zl_sublist 0 i v) (zl_singleton i v0)) (zl_sublist (i + 1) n v) *)
  | Tstruct id _, StructField i =>
      fun v v0 => upd_compact_prod _ v (i, field_type i (co_members (get_co id))) v0 member_dec
  | Tunion id _, UnionField i =>
      fun v v0 => upd_compact_sum _ v (i, field_type i (co_members (get_co id))) v0 member_dec
  | _, _ => fun v _ => v
  end (unfold_reptype v) v0).

Fixpoint upd_reptype (t: type) (gfs: list gfield) (v: reptype t) (v0: reptype (nested_field_type t gfs)): reptype t :=
  match gfs as gfs'
    return reptype (match gfs' with
                    | nil => t
                    | gf :: gfs0 => gfield_type (nested_field_type t gfs0) gf
                    end) -> reptype t
  with
  | nil => fun v0 => v0
  | gf :: gfs0 => fun v0 => upd_reptype t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0)
  end (eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t gfs))).

Lemma upd_Znth_ints i xints v:
      upd_Znth i (map Vint xints) (Vint v) =
      map Vint ((sublist 0 i xints) ++
                v :: (sublist (i + 1) (Zlength (map Vint xints)) xints)).
Proof. unfold upd_Znth; intros. rewrite map_app. simpl.
  do 2 rewrite sublist_map; trivial.
Qed.

Lemma upd_reptype_data_equal: forall t gfs v v0 v1, data_equal v0 v1 -> data_equal (upd_reptype t gfs v v0) (upd_reptype t gfs v v1).
Proof.
  intros.
  induction gfs as [| gf gfs].
  + exact H.
  + change (upd_reptype t (gf :: gfs) v v0) with
      (upd_reptype t gfs v (upd_gfield_reptype _ gf (proj_reptype t gfs v)
        (eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gf :: gfs)))))).
    change (upd_reptype t (gf :: gfs) v v1) with
      (upd_reptype t gfs v (upd_gfield_reptype _ gf (proj_reptype t gfs v)
        (eq_rect_r reptype v1 (eq_sym (nested_field_type_ind t (gf :: gfs)))))).
    apply IHgfs.
    assert (data_equal (eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gf :: gfs))))
              (eq_rect_r reptype v1 (eq_sym (nested_field_type_ind t (gf :: gfs)))))
      by (apply eq_rect_r_data_equal; auto).
    forget (eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gf :: gfs)))) as V0.
    forget (eq_rect_r reptype v1 (eq_sym (nested_field_type_ind t (gf :: gfs)))) as V1.
    forget (proj_reptype t gfs v) as V.
    clear - H0.
    revert V0 V1 H0 V.
    destruct (nested_field_type t gfs), gf; unfold upd_gfield_reptype; intros; try reflexivity.
Abort.
End SINGLE_HOLE.

Module zlist_hint_db.

Lemma Znth_sub_0_r: forall A {d: Inhabitant A} i l, Znth (i - 0) l = Znth i l.
  intros.
  rewrite Z.sub_0_r by omega.
  auto.
Qed.

Lemma Znth_map_Vint: forall (i : Z) (l : list int),
  0 <= i < Zlength l -> Znth i (map Vint l) = Vint (Znth i l).
Proof.
  intros i l.
  apply Znth_map.
Qed.

End zlist_hint_db.

(*Hint Rewrite @zl_constr_correct using solve [omega] : zl_nth_db.
Hint Rewrite zlist_hint_db.Znth_sub_0_r : zl_nth_db.
Hint Rewrite zlist_hint_db.Znth_map_Vint using solve [omega] : zl_nth_db.
Hint Rewrite (fun A d => @zl_sublist_correct A d _ (list_zlist_correct _ _)) using solve [omega] : zl_nth_db.
Hint Rewrite (fun A d => @zl_concat_correct_l A d _ (list_zlist_correct _ _)) using solve [omega] : zl_nth_db.
Hint Rewrite (fun A d => @zl_concat_correct_r A d _ (list_zlist_correct _ _)) using solve [omega] : zl_nth_db.

Hint Rewrite (fun A d => @zl_sub_concat_l A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_concat_r A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_concat_mid A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_sub A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_self A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_sub_empty A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_concat_empty_l A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
Hint Rewrite (fun A d => @zl_concat_empty_r A d _ (list_zlist_correct _ _)) using solve [omega] : zl_sub_db.
*)
Section POSE_TAC.

Context {cs: compspecs}.

Definition eq_pose {A} x y := @eq A x y.

Definition abs_pose t (v: reptype t) : Prop := True.

Definition concr_pose t (v: reptype t) : Prop := True.

End POSE_TAC.

Ltac abs_or_concr t v :=
  let t' := eval compute in t in
  match t' with
  | Tarray _ _ _ =>
    match v with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: _ => assert (concr_pose t v) by exact I
    | _ => assert (abs_pose t v) by exact I
    end
  | Tstruct ?id _ =>
    let m := eval compute in (co_members (get_co id)) in
    match m with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: @nil _ => assert (concr_pose t v) by exact I
    | _ => match v with
           | (_, _) => assert (concr_pose t v) by exact I
           | _ => assert (abs_pose t v) by exact I
           end
    end
  | Tunion ?id _ =>
    let m := eval compute in (co_members (get_co id)) in
    match m with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: @nil _ => assert (concr_pose t v) by exact I
    | _ => match v with
           | (_, _) => assert (concr_pose t v) by exact I
           | _ => assert (abs_pose t v) by exact I
           end
    end
  end.

Transparent peq.

Ltac cbv_proj_struct H :=
    cbv beta zeta iota delta
    [proj_struct proj_compact_prod list_rect
    member_dec field_type Ctypes.field_type
     ident_eq peq Pos.eq_dec BinNums.positive_rec positive_rect
    sumbool_rec sumbool_rect bool_dec bool_rec bool_rect option_rec option_rect
    eq_rect_r eq_rect eq_rec_r eq_rec eq_sym eq_trans f_equal
    type_eq type_rec type_rect typelist_eq typelist_rec typelist_rect
    intsize_rec intsize_rect signedness_rec signedness_rect floatsize_rec floatsize_rect
    tvoid tschar tuchar tshort tushort tint
    tuint tbool tlong tulong tfloat tdouble tptr tarray noattr
    ] in H; simpl in H.

Ltac pose_proj_reptype_1 CS t gf v H :=
  assert (@proj_gfield_reptype CS t gf v = @proj_gfield_reptype CS t gf v) as H by reflexivity;
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let V := fresh "v" in
  let t' := eval compute in t in
  remember v as V eqn:H0 in H at 2;
  match type of V with
  | ?t_temp => change t_temp with (@reptype CS t) in V
  end;
  change (@proj_gfield_reptype CS t gf V) with (@proj_gfield_reptype CS t' gf V) in H;
  unfold proj_gfield_reptype in H at 2;
  pose proof unfold_reptype_JMeq t' V as H1;
  apply JMeq_eq in H1;
  rewrite H1 in H; clear H1;
  match type of H with
  | _ = proj_struct ?i ?m V ?d =>
    let v_res := fresh "v" in
    let H_eq := fresh "H" in
    remember (proj_struct i m V d) as v_res eqn:H_eq;
    let d' := eval vm_compute in d in change d with d' in H_eq;
    let m' := eval vm_compute in m in change m with m' in H_eq;
    cbv_proj_struct H_eq;
    subst v_res;
    subst V
(*  | _ = zl_nth ?i ?l =>
    subst V;
    autorewrite with zl_nth_db in H
*)
  | _ =>
    subst V
  end
.

Ltac pose_proj_reptype CS t gfs v H :=
  match gfs with
  | nil =>
      assert (eq_pose (@proj_reptype CS t gfs v) v) as H by reflexivity
  | ?gf :: ?gfs0 =>
     pose proof I as H;   (* *0* SEE LINE *1* *)
     let H0 := fresh "H" in
     pose_proj_reptype CS t gfs0 v H0;
     match type of H0 with
     | eq_pose (proj_reptype t gfs0 v) ?v0 =>
         let H1 := fresh "H" in
         match gfs0 with
         | nil => pose_proj_reptype_1 CS t gf v0 H1
         | _ => pose_proj_reptype_1 CS (nested_field_type t gfs0) gf v0 H1
         end;
         clear H;         (* *1* SEE LINE *0* *)
         match gfs0 with
         | nil => assert (eq_pose (@proj_reptype CS t gfs v) (@proj_gfield_reptype CS t gf v0)) as H
         | _ => assert (eq_pose (@proj_reptype CS t gfs v)
                   (@proj_gfield_reptype CS (nested_field_type t gfs0) gf v0)) as H
         end;
         [unfold eq_pose in *; rewrite <- H0; unfold proj_reptype, eq_rect_r; apply eq_sym, eq_rect_eq |];
         rewrite H1 in H;
         clear H1
     end
  end.

Ltac pose_upd_reptype_1 CS t gf v v0 H :=
  let t' := eval compute in t in
  assert (data_equal (@upd_gfield_reptype CS t gf v v0) (@upd_gfield_reptype CS t' gf v v0)) as H
    by reflexivity;
  unfold upd_gfield_reptype at 2 in H;
  let H0 := fresh "H" in
  pose proof unfold_reptype_JMeq t' v as H0;
  apply JMeq_eq in H0;
  rewrite H0 in H;
  clear H0;
  match t' with
  | Tarray _ _ _ => autorewrite with zl_sub_db in H
  | _ => idtac
  end;
  unfold upd_compact_prod, eq_rect_r in H; simpl in H;
  match type of H with
  | data_equal _ (fold_reptype ?v_res) =>
    pose proof (JMeq_eq (fold_reptype_JMeq t' v_res)) as H0;
    rewrite H0 in H;
    clear H0
  end.
(*
Ltac pose_upd_reptype CS t gfs v v0 H :=
  match gfs with
  | nil =>
      assert (data_equal (@upd_reptype CS t gfs v v0) v0) as H by reflexivity
  | ?gf :: ?gfs0 =>
      pose proof I as H;   (* *2* SEE LINE *3* *)
      match goal with
      | HH : eq_pose (proj_reptype t gfs0 v) ?v1 |- _ =>
          let H_upd1 := fresh "H_upd1" in
          pose_upd_reptype_1 CS (nested_field_type t gfs0) gf v1 v0 H_upd1;
          match type of H_upd1 with
          | data_equal _ ?v1' =>
                  let H0 := fresh "H" in
                  pose_upd_reptype CS t gfs0 v v1' H0;
                  match type of H0 with
                  | data_equal _ ?v_res =>
                      clear H;         (* *3* SEE LINE *2* *)
                      assert (H: data_equal (@upd_reptype CS t gfs v v0) v_res);
                          [| clear H_upd1 H0]
                  end;
                 [change (@upd_reptype CS t gfs v v0) with
                   (@upd_reptype CS t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0));
                  unfold eq_pose in HH; rewrite HH;
                  eapply Equivalence.equiv_transitive;
                  [apply upd_reptype_data_equal; exact H_upd1 | exact H0]
                 | clear HH]
          end
      end
  end.
*)
Module Type TestType.
End TestType.

(*
Module Test : TestType.

Definition _f1 := 1%positive.
Definition _f2 := 2%positive.
Definition _f3 := 3%positive.
Definition _f4 := 4%positive.
Definition _f5 := 5%positive.
Definition cd1 := Composite 101%positive Struct ((_f1, tint) :: (_f2%positive, tint) :: nil) noattr.
Definition cd2 := Composite 102%positive Struct ((_f3, Tstruct 101%positive noattr) ::
                                 (_f4, Tstruct 101%positive noattr) ::
                                 (_f5, Tpointer (Tstruct 101%positive noattr) noattr) :: nil) noattr.
Definition cenv := match build_composite_env (cd1 :: cd2 :: nil) with Errors.OK env => env | _ => PTree.empty _ end.

Instance cs: compspecs.
  apply (mkcompspecs cenv).
+
  apply build_composite_env_consistent with (defs := cd1 :: cd2 :: nil).
  reflexivity.
  + intros ? ? ?.
    apply PTree.elements_correct in H.
    revert H.
    change co with (snd (id, co)) at 2.
    forget (id, co) as ele.
    revert ele.
    apply Forall_forall.
    assert (8 >= 8) by omega.
    assert (4 >= 4) by omega.
    repeat constructor; unfold composite_legal_alignas; assumption.
  + intros ? ? ?.
    apply PTree.elements_correct in H.
    revert H.
    change co with (snd (id, co)) at 2.
    forget (id, co) as ele.
    revert ele.
    apply Forall_forall.
    repeat constructor; unfold composite_legal_alignas; reflexivity.
Defined.

Definition t1 := Tstruct 101%positive noattr.
Definition t2 := Tstruct 102%positive noattr.
Definition v1: reptype t1 := (Vint Int.zero, Vint Int.one).
Definition v2: reptype t2 := ((Vint Int.zero, Vint Int.one), ((Vint Int.zero, Vint Int.one), Vundef)).

(*
Eval vm_compute in (reptype_gen t2).
Eval vm_compute in (proj_reptype t1 (StructField 1%positive :: nil) v1).
*)
Goal proj_reptype t1 (StructField _f1 :: nil) v1 = Vint Int.zero.
reflexivity.
Qed.

Goal proj_reptype t2 (StructField _f2 :: StructField _f3 :: nil) v2 = Vint Int.one.
unfold v2.
pose_proj_reptype cs t2
  (StructField _f2 :: StructField _f3 :: nil) ((Vint Int.zero, Vint Int.one, (Vint Int.zero, Vint Int.one, Vundef)): reptype (Tstruct 102%positive noattr)) HH.
eauto.
Time Qed. (* Cut down from 10 seconds to 4 seconds, magically. *)

Goal forall n l, 0 < n -> proj_reptype (tarray tint n) (ArraySubsc 0 :: nil) l = Znth 0 l Vundef.
intros.
pose_proj_reptype cs (tarray tint n) (ArraySubsc 0 :: nil) l HH.
exact HH.
Qed.

Goal data_equal (upd_reptype t2 (StructField 3%positive :: nil) v2 (Vint Int.one, Vint Int.one))
((Vint Int.one, Vint Int.one), ((Vint Int.zero, Vint Int.one), Vundef)).
set (v0 := (Vint Int.one, Vint Int.one)).
change (val * val)%type with (reptype (Tstruct 101%positive noattr)) in v0.
pose_proj_reptype cs (Tstruct 102%positive noattr) (StructField 3%positive :: nil) v2 H.
pose_upd_reptype cs (Tstruct 102%positive noattr) (StructField 3%positive :: nil) v2 v0 H1.
exact H1.
Qed.

Goal forall n l, 0 < n -> data_equal
    (upd_reptype (tarray tint n) (ArraySubsc 0 :: nil) l Vundef)
    (Vundef :: sublist 1 (Zlength l) l).
intros.
pose_proj_reptype cs (tarray tint n) (ArraySubsc 0 :: nil) l HH.
pose_upd_reptype cs (tarray tint n) (ArraySubsc 0 :: nil) l Vundef HHH.
exact HHH.
Qed.

End Test.

*)