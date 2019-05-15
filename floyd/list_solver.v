Require Import VST.floyd.base2.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.field_compat.
Import ListNotations.


(* solve list equations *)
(* interpreted functions :
  Zlength
  app
  list_repeat / Zrepeat
  map
  sublist
  upd_Znth -> sublist
  Znth
*)

Lemma repeat_list_repeat : forall {A : Type} (n : nat) (x : A),
  repeat x n = list_repeat n x.
Proof. intros. induction n; simpl; try f_equal; auto. Qed.

Definition Zrepeat {A : Type} (n : Z) (x : A) : list A :=
  repeat x (Z.to_nat n).

Lemma Zlength_Zrepeat : forall (A : Type) (n : Z) (x : A),
  0 <= n ->
  Zlength (Zrepeat n x) = n.
Proof. intros *. unfold Zrepeat. rewrite repeat_list_repeat. apply @Zlength_list_repeat. Qed.

Ltac Zlength_solve := autorewrite with Zlength; pose_Zlength_nonneg; omega.
Hint Rewrite Zlength_cons : Zlength.
Hint Rewrite Zlength_nil : Zlength.
Hint Rewrite Zlength_app : Zlength.
Hint Rewrite Zlength_map : Zlength.
Hint Rewrite Zlength_Zrepeat using Zlength_solve : Zlength.
Hint Rewrite @Zlength_list_repeat using Zlength_solve : Zlength.
Hint Rewrite @upd_Znth_Zlength using Zlength_solve : Zlength.
Hint Rewrite @Zlength_sublist using Zlength_solve : Zlength.

(******** list_form *************)
Lemma Zrepeat_fold : forall (A : Type) (n : Z) (x : A),
  list_repeat (Z.to_nat n) x = Zrepeat n x.
Proof. intros *. rewrite <- repeat_list_repeat. auto. Qed.

Lemma cons_Zrepeat_1_app : forall (A : Type) (x : A) (al : list A),
  x :: al = Zrepeat 1 x ++ al.
Proof. auto. Qed.

Lemma upd_Znth_unfold : forall (A : Type) (n : Z) (al : list A) (x : A),
  upd_Znth n al x = sublist 0 n al ++ [x] ++ sublist (n+1) (Zlength al) al.
Proof. auto. Qed.

(* this seems not needed *)
(*Lemma Znth_Zrepeat_1_sublist : forall (A : Type) (d : Inhabitant A) (i : Z) (al : list A),
  0 <= i < Zlength al ->
  Zrepeat 1 (Znth i al) = sublist i (i+1) al.
Proof. intros. rewrite sublist_one by omega; auto. Qed. *)

Hint Rewrite Zrepeat_fold upd_Znth_unfold cons_Zrepeat_1_app : list_form_rewrite.
(* Hint Rewrite Znth_Zrepeat_1_sublist using Zlength_solve: list_form_rewrite. *)
Hint Rewrite app_nil_r app_nil_l : list_form_rewrite.

Ltac list_form :=
  autorewrite with list_form_rewrite in *.

(* handling of map is not in list_form now *)
(*
Lemma Znth_map2 : forall (B : Type) (db : Inhabitant B) (A : Type) (da : Inhabitant A) (i : Z) (f : A -> B) (al : list A),
  0 <= i < Zlength al ->
  Znth i (map f al) = f (Znth i al).
Proof. intros. apply Znth_map; auto. Qed.

Hint Rewrite <- (@Znth_map2 float32 Inhabitant_float32) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 ptrofs Inhabitant_ptrofs) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 int64 Inhabitant_int64) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 byte Inhabitant_byte) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 int Inhabitant_int) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 val Inhabitant_val) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 Z Inhabitant_Z) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 nat Inhabitant_nat) using Zlength_solve : list_form.
*)

(*********************** Znth_solve *******************************)
Lemma Znth_Zrepeat : forall (A : Type) (d : Inhabitant A) (i n : Z) (x : A),
  0 <= i < n ->
  Znth i (Zrepeat n x) = x.
Proof. intros. unfold Zrepeat. rewrite repeat_list_repeat. apply Znth_list_repeat_inrange; auto. Qed.

Hint Rewrite @Znth_list_repeat_inrange using Zlength_solve : Znth.
Hint Rewrite @Znth_sublist using Zlength_solve : Znth.
Hint Rewrite app_Znth1 app_Znth2 using Zlength_solve : Znth.
Hint Rewrite Znth_Zrepeat using Zlength_solve : Znth.

Hint Rewrite (@Znth_map _ Inhabitant_float) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_float32) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_ptrofs) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_int64) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_byte) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_int) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_val) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_Z) using Zlength_solve : Znth.
Hint Rewrite (@Znth_map _ Inhabitant_nat) using Zlength_solve : Znth.

Create HintDb Znth_solve_hint.

Ltac Znth_solve_rec :=
  autorewrite with Znth;
  autorewrite with Zlength;
  auto with Znth_solve_hint;
  try match goal with
  | |- context [Znth ?n (app ?al ?bl)] =>
    let H := fresh in
    pose (H := Z_lt_le_dec n (Zlength al));
    autorewrite with Zlength in H; destruct H;
    Znth_solve_rec
  end.

Ltac Znth_solve :=
  autorewrite with Zlength in *;
  Znth_solve_rec.

(**************** Znth_solve2 is Znth_solve in * ***************)
Ltac Znth_solve2 :=
  autorewrite with Zlength in *; autorewrite with Znth in *; try Zlength_solve; try congruence; (* try solve [exfalso; auto]; *)
  try first
  [ match goal with
    | |- context [ Znth ?n (?al ++ ?bl) ] =>
          let H := fresh in
          pose (H := Z_lt_le_dec n (Zlength al)); autorewrite with Zlength in *; destruct H; Znth_solve2
    end
  | match goal with
    | H0 : context [ Znth ?n (?al ++ ?bl) ] |- _ =>
          let H := fresh in
          pose (H := Z_lt_le_dec n (Zlength al)); autorewrite with Zlength in *; destruct H; Znth_solve2
    end
  ].

(*************** list extentionality *************)
Lemma nth_eq_ext : forall (A : Type) (default : A) (al bl : list A),
  length al = length bl ->
  (forall (i : nat), (0 <= i < length al)%nat -> nth i al default = nth i bl default) ->
  al = bl.
Proof.
  intros. generalize dependent bl.
  induction al; intros;
    destruct bl; try discriminate; auto.
  f_equal.
  - apply (H0 0%nat). simpl. omega.
  - apply IHal.
    + simpl in H. omega.
    + intros. apply (H0 (S i)). simpl. omega.
Qed.

Lemma Znth_eq_ext : forall {A : Type} {d : Inhabitant A} (al bl : list A),
  Zlength al = Zlength bl ->
  (forall (i : Z), 0 <= i < Zlength al -> Znth i al = Znth i bl) ->
  al = bl.
Proof.
  intros. rewrite !Zlength_correct in *. apply nth_eq_ext with d.
  - omega.
  - intros. rewrite  <- (Nat2Z.id i).
    specialize (H0 (Z.of_nat i) ltac:(omega)).
    rewrite !nth_Znth by (rewrite !Zlength_correct in *; omega).
    apply H0.
Qed.

Definition data_subsume {cs : compspecs} (t : type) (x y : reptype t) : Prop :=
  forall sh p, data_at sh t x p |-- data_at sh t y p.

Lemma data_subsume_refl : forall {cs : compspecs} (t : type) (x : reptype t),
  data_subsume t x x.
Proof. unfold data_subsume. intros. auto. Qed.

Lemma data_subsume_refl' : forall {cs : compspecs} (t : type) (x x' : reptype t),
  x = x' ->
  data_subsume t x x'.
Proof. unfold data_subsume. intros. cancel. Qed.

Lemma data_subsume_default : forall {cs : compspecs} (t : type) (x y : reptype t),
  y = default_val t ->
  data_subsume t x y.
Proof. unfold data_subsume. intros. subst y. apply data_at_data_at_. Qed.

Hint Resolve data_subsume_refl data_subsume_refl' data_subsume_default.

Lemma data_subsume_array_ext : forall {cs : compspecs} (t : type) (n : Z) (al bl : list (reptype t)),
  n = Zlength al ->
  n = Zlength bl ->
  (forall (i : Z), 0 <= i < n -> data_subsume t (Znth i al) (Znth i bl)) ->
  data_subsume (tarray t n) al bl.
Proof.
  intros.
  generalize dependent bl.
  generalize dependent n.
  induction al; intros; destruct bl as [ | b bl];
    autorewrite with list_form_rewrite Zlength in *; try Zlength_solve;
    unfold data_subsume; intros.
  - (* al = [] /\ bl = [] *)
    entailer!.
  - (* al <> [] /\ bl <> [] *)
    do 2 rewrite split2_data_at_Tarray_app with (mid := 1) by Zlength_solve.
    apply sepcon_derives.
    + specialize (H1 0 ltac:(Zlength_solve)).
      autorewrite with Znth in H1.
      rewrite data_at_singleton_array_eq with (v := a) by auto.
      rewrite data_at_singleton_array_eq with (v := b) by auto.
      apply H1.
    + apply IHal; try Zlength_solve.
      intros. specialize (H1 (i+1) ltac:(Zlength_solve)).
      autorewrite with Znth in H1.
      autorewrite with Zlength norm in H1.
      replace (i + 1 - 1) with i in H1 by omega.
      apply H1.
Qed.

Ltac apply_list_ext :=
  first
  [ apply data_subsume_array_ext;
    only 1, 2 : Zlength_solve
  | match goal with |- @eq ?list_A _ _ =>
      match eval compute in list_A with list ?A =>
        apply (@Znth_eq_ext A ltac:(auto with typeclass_instances))
      end
    end;
    only 1 : Zlength_solve
  ];
  autorewrite with Zlength;
  intros.

(*************** fapply & fassumption *************)
Lemma imp_refl' : forall P Q : Prop,
  P = Q -> P -> Q.
Proof. intros. congruence. Qed.

Ltac fapply H :=
  match type of H with ?HH =>
  eapply (imp_refl' HH); only 2 : exact H
  end.

Ltac fassumption :=
  first
  [ assumption
  | match goal with
    | H : _ |- _ => fapply H; repeat f_equal; match goal with |- (_ = _)%Z => idtac end; Zlength_solve
    end
  ].

(******************* eq_solve ********************)
Ltac eq_solve_with tac :=
  solve [
  repeat multimatch goal with
  | |- @eq Z _ _ => omega
  | |- @eq (_ -> _) _ _ => apply functional_extensionality; intros
  | |- _ <-> _ => apply prop_unext
  | _ => f_equal
  | _ => tac
  end
  ].

Tactic Notation "eq_solve" "with" tactic(tac) := eq_solve_with (tac).
Tactic Notation "eq_solve" := eq_solve with fail.

Hint Extern 1 (@eq _ _ _) => eq_solve : Znth_solve_hint.
(* Hint Extern 1 (@eq _ _ _) => fassumption : Znth_solve_hint.
Hint Extern 1 (@eq _ _ _) => congruence : Znth_solve_hint. *)

(*************** list_solve2 **********************)
Ltac list_solve2' :=
  repeat match goal with [ |- _ /\ _ ] => split end;
  intros;
  try Zlength_solve;
  list_form; autorewrite with Zlength in *; Znth_solve2;
  auto with Znth_solve_hint;
  first
  [ fassumption
  | Zlength_solve
  | apply_list_ext; Znth_solve
  ];
  auto with Znth_solve_hint;
  try fassumption.

Ltac list_solve2 :=
  list_solve2';
  fail "list_solve2 cannot solve this goal".

(*************** range definitions **********************)
Definition rangei (lo hi : Z) (P : Z -> Prop) :=
  forall i, lo <= i < hi -> P i.

Definition range_uni {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : A -> Prop) :=
  rangei lo hi (fun i => P (Znth i l)).

Definition rangei_uni {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : Z -> A -> Prop) :=
  rangei lo hi (fun i => P i (Znth i l)).

Definition range_bin {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop) :=
  rangei lo hi (fun i => P (Znth i al) (Znth (i + offset) bl)).

(****************** range lemmas ************************)

Lemma rangei_split : forall (lo mi hi : Z) (P : Z -> Prop),
  lo <= mi <= hi ->
  rangei lo hi P <-> rangei lo mi P /\ rangei mi hi P.
Proof.
  intros. unfold rangei. split; intros.
  - (* -> *)
    split; intros; apply H0; omega.
  - (* <- *)
    destruct H0.
    destruct (Z_lt_le_dec i mi).
    + apply H0; omega.
    + apply H2; omega.
Qed.

Lemma rangei_implies : forall (lo hi : Z) (P Q : Z -> Prop),
  rangei lo hi (fun i => P i -> Q i) ->
  rangei lo hi P ->
  rangei lo hi Q.
Proof. unfold rangei; intros; auto. Qed.

Lemma rangei_iff : forall (lo hi : Z) (P Q : Z -> Prop),
  rangei lo hi (fun i => P i <-> Q i) ->
  rangei lo hi P <-> rangei lo hi Q.
Proof.
  intros. split; apply rangei_implies; unfold rangei in *; intros; apply H; auto.
Qed.

Lemma rangei_shift : forall (lo hi offset : Z) (P : Z -> Prop),
  rangei lo hi P <-> rangei (lo + offset) (hi + offset) (fun i => P (i - offset)).
Proof.
  intros. unfold rangei. split; intros.
  - (* -> *)
    apply H; omega.
  - (* <- *)
    replace i with (i + offset - offset) by omega.
    apply H; omega.
Qed.

Lemma rangei_and : forall (lo hi : Z) (P Q : Z -> Prop),
  rangei lo hi (fun i => P i /\ Q i) <->
  rangei lo hi P /\ rangei lo hi Q.
Proof.
  unfold rangei; intros; split; intros.
  + split; intros; specialize (H i ltac:(assumption)); tauto.
  + destruct H. auto.
Qed.

Lemma rangei_shift' : forall (lo hi lo' hi' : Z) (P Q : Z -> Prop),
  let offset := lo' - lo in
  offset = hi' - hi ->
  rangei lo' hi' (fun i => Q i <-> P (i - offset)) ->
  rangei lo hi P <-> rangei lo' hi' Q.
Proof.
  intros.
  (* replace (fun i : Z => Q i <-> P (i - offset))
  with (fun i => (fun i => Q i -> P (i - offset)) i /\ (fun i => P (i - offset) -> Q i) i) in H0 by reflexivity.
  rewrite rangei_and in H0. destruct H0. *)
  replace lo' with (lo + offset) by omega.
  replace hi' with (hi + offset) by omega.
  rewrite rangei_iff with (P := Q) (Q := fun i => P (i - offset)) by fassumption.
  apply rangei_shift.
Qed.

Lemma range_uni_app1 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  range_uni lo hi (al ++ bl) P <->
  range_uni lo hi al P.
Proof.
  unfold range_uni. intros. apply rangei_iff.
  unfold rangei. intros. apply prop_unext, f_equal. Znth_solve.
Qed.

Lemma range_uni_app2 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  range_uni lo hi (al ++ bl) P ->
  range_uni (lo - Zlength al) (hi - Zlength al) bl P.
Proof.
  unfold range_uni. intros. eapply rangei_shift'. 3 : apply H0.
  + omega.
  + unfold rangei. intros. apply prop_unext, f_equal. Znth_solve.
Qed.

Lemma range_uni_app : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  range_uni lo hi (al ++ bl) P ->
  range_uni lo (Zlength al) al P /\
  range_uni 0 (hi - Zlength al) bl P.
Proof.
  unfold range_uni. intros. split; intro; intros.
  - specialize (H0 i ltac:(omega)). simpl in H0. autorewrite with Znth in H0. apply H0.
  - specialize (H0 (i + Zlength al) ltac:(omega)). simpl in H0. autorewrite with Znth in H0. fassumption.
Qed.

Lemma range_uni_sublist : forall {A : Type} {d : Inhabitant A} (lo hi lo' hi' : Z) (l : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  range_uni lo hi (sublist lo' hi' l) P ->
  range_uni (lo+lo') (hi+lo') l P.
Proof.
  unfold range_uni, rangei. intros.
  fapply (H0 (i - lo') ltac:(omega)). f_equal. Znth_solve.
Qed.

Lemma range_uni_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi : Z) (l : list A) (f : A -> B) (P : B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  range_uni lo hi (map f l) P ->
  range_uni lo hi l (fun x => P (f x)).
Proof.
  unfold range_uni, rangei. intros.
  fapply (H0 i ltac:(omega)). f_equal. rewrite Znth_map by omega. auto.
Qed.

Lemma range_uni_Zrepeat : forall {A : Type} {d : Inhabitant A} (lo hi n : Z) (x : A) (P : A -> Prop),
  0 <= lo < hi /\ hi <= n ->
  range_uni lo hi (Zrepeat n x) P ->
  P x.
Proof.
  unfold range_uni, rangei. intros.
  fapply (H0 lo ltac:(omega)). f_equal. Znth_solve.
Qed.

Lemma range_uni_empty : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : A -> Prop),
  lo = hi ->
  range_uni lo hi l P <->
  True.
Proof.
  intros; split; unfold range_uni, rangei; intros; auto; omega.
Qed.

Lemma rangei_uni_app1 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : Z -> A -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  rangei_uni lo hi (al ++ bl) P <->
  rangei_uni lo hi al P.
Proof.
  unfold rangei_uni. intros. apply rangei_iff.
  unfold rangei. intros. apply prop_unext. f_equal. Znth_solve.
Qed.

Lemma rangei_uni_app2 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : Z -> A -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  rangei_uni lo hi (al ++ bl) P ->
  rangei_uni (lo - Zlength al) (hi - Zlength al) bl (fun i => P (i + Zlength al)).
Proof.
  unfold rangei_uni. intros. eapply rangei_shift'. 3 : apply H0.
  + omega.
  + unfold rangei. intros. apply prop_unext. f_equal.
    - omega.
    - Znth_solve.
Qed.

Lemma rangei_uni_app : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : Z -> A -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  rangei_uni lo hi (al ++ bl) P ->
  rangei_uni lo (Zlength al) al P /\
  rangei_uni 0 (hi - Zlength al) bl (fun i => P (i + Zlength al)).
Proof.
  unfold rangei_uni. intros. split; intro; intros.
  - specialize (H0 i ltac:(omega)). simpl in H0. autorewrite with Znth in H0. apply H0.
  - specialize (H0 (i + Zlength al) ltac:(omega)). simpl in H0. autorewrite with Znth in H0. fassumption.
Qed.

Lemma rangei_uni_sublist : forall {A : Type} {d : Inhabitant A}
  (lo hi lo' hi' : Z) (l : list A) (P : Z -> A -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  rangei_uni lo hi (sublist lo' hi' l) P ->
  rangei_uni (lo+lo') (hi+lo') l (fun i => P (i - lo')).
Proof.
  unfold rangei_uni, rangei. intros.
  fapply (H0 (i - lo') ltac:(omega)). f_equal. Znth_solve.
Qed.

Lemma rangei_uni_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi : Z) (l : list A) (f : A -> B) (P : Z -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  rangei_uni lo hi (map f l) P ->
  rangei_uni lo hi l (fun i x => P i (f x)).
Proof.
  unfold rangei_uni, rangei. intros.
  fapply (H0 i ltac:(omega)). f_equal. rewrite Znth_map by omega. auto.
Qed.

Lemma rangei_uni_Zrepeat : forall {A : Type} {d : Inhabitant A} (lo hi n : Z) (x : A) (P : Z -> A -> Prop),
  0 <= lo < hi /\ hi <= n ->
  rangei_uni lo hi (Zrepeat n x) P ->
  rangei lo hi (fun i => P i x).
Proof.
  unfold rangei_uni, rangei. intros.
  fapply (H0 i ltac:(omega)). f_equal. Znth_solve.
Qed.

Lemma rangei_uni_empty : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : Z -> A -> Prop),
  lo = hi->
  rangei_uni lo hi l P <->
  True.
Proof.
  intros; split; unfold rangei_uni, rangei; intros; auto; omega.
Qed.

Lemma range_bin_rangei_uniA : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop),
  range_bin lo hi offset al bl P <->
  rangei_uni lo hi al (fun i x => P x (Znth (i + offset) bl)).
Proof.
  unfold range_bin, rangei_uni, rangei. reflexivity.
Qed.

Lemma range_bin_rangei_uniB : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop),
  range_bin lo hi offset al bl P <->
  rangei_uni (lo+offset) (hi+offset) bl (fun i => P (Znth (i - offset) al)).
Proof.
  unfold range_bin, rangei_uni.
  intros. split; intros.
  + eapply rangei_shift'. 3 : exact H.
    - omega.
    - unfold rangei. intros. eq_solve.
  + eapply rangei_shift'. 3 : exact H.
    - eq_solve.
    - unfold rangei. intros. eq_solve.
Qed.

Lemma range_binA_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  range_bin lo hi offset (al ++ bl) l' P <->
  range_bin lo hi offset al l' P.
Proof.
  intros *. do 2 rewrite range_bin_rangei_uniA. apply rangei_uni_app1.
Qed.

Lemma range_binA_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  range_bin lo hi offset (al ++ bl) l' P ->
  range_bin (lo - Zlength al) (hi - Zlength al) (offset + Zlength al) bl l' P.
Proof.
  intros *. do 2 rewrite range_bin_rangei_uniA. intros.
  apply rangei_uni_app2 in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma range_binA_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (al bl : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength al + Zlength bl ->
  range_bin lo hi offset (al ++ bl) l' P ->
  range_bin lo (Zlength al) offset al l' P /\
  range_bin 0 (hi - Zlength al) (offset + Zlength al) bl l' P.
Proof.
  intros *. do 3 rewrite range_bin_rangei_uniA. intros.
  apply rangei_uni_app in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma range_binA_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi lo' hi' offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo <= hi /\ hi <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l ->
  range_bin lo hi offset (sublist lo' hi' l) l' P ->
  range_bin (lo+lo') (hi+lo') (offset-lo') l l' P.
Proof.
  intros *. do 2 rewrite range_bin_rangei_uniA. intros.
  apply rangei_uni_sublist in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma range_binA_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (lo hi offset : Z) (l : list A) (l' : list B) (f : A -> C) (P : C -> B -> Prop),
  0 <= lo <= hi /\ hi <= Zlength l ->
  range_bin lo hi offset (map f l) l' P ->
  range_bin lo hi offset l l' (fun x => P (f x)).
Proof.
  unfold range_bin, rangei. intros.
  fapply (H0 i ltac:(omega)).
  eq_solve with (rewrite Znth_map by omega).
Qed.

Lemma range_binA_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi n offset : Z) (x : A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo < hi /\ hi <= n ->
  range_bin lo hi offset (Zrepeat n x) l' P ->
  range_uni (lo + offset) (hi + offset) l' (P x).
Proof.
  unfold range_bin, range_uni. intros.
  eapply rangei_shift'. 3 : exact H0.
  + omega.
  + unfold rangei. intros. eq_solve with Znth_solve.
Qed.

Lemma range_bin_empty : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  lo = hi ->
  range_bin lo hi offset l l' P <->
  True.
Proof.
  intros; split; unfold range_bin, rangei; intros; auto; omega.
Qed.

Lemma range_binB_app1 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= Zlength al' ->
  range_bin lo hi offset l (al' ++ bl') P <->
  range_bin lo hi offset l al' P.
Proof.
  intros *. do 2 rewrite range_bin_rangei_uniB. apply rangei_uni_app1.
Qed.

Lemma range_binB_app2 : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  Zlength al' <= lo + offset <= hi + offset /\ hi + offset <= Zlength al' + Zlength bl' ->
  range_bin lo hi offset l (al' ++ bl') P ->
  range_bin lo hi (offset - Zlength al') l bl' P.
Proof.
  intros *. do 2 rewrite range_bin_rangei_uniB. intros.
  apply rangei_uni_app2 in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma range_binB_app : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi offset : Z) (l : list A) (al' bl' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= Zlength al' /\ Zlength al' <= hi + offset <= Zlength al' + Zlength bl' ->
  range_bin lo hi offset l (al' ++ bl') P ->
  range_bin lo (Zlength al' - offset) offset l al' P /\
  range_bin (Zlength al' - offset) hi (offset - Zlength al') l bl' P.
Proof.
  intros *. do 3 rewrite range_bin_rangei_uniB. intros.
  apply rangei_uni_app in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma range_binB_sublist : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi lo' hi' offset : Z) (l : list A) (l' : list B) (P : A -> B -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= hi' - lo' /\ 0 <= lo' <= hi' /\ hi' <= Zlength l' ->
  range_bin lo hi offset l (sublist lo' hi' l') P ->
  range_bin lo hi (offset + lo') l l' P.
Proof.
  intros *. do 2 rewrite range_bin_rangei_uniB. intros.
  apply rangei_uni_sublist in H0. 2 : assumption.
  fapply H0. eq_solve.
Qed.

Lemma range_binB_map : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B} {C : Type} {dc : Inhabitant C}
  (lo hi offset : Z) (l : list A) (l' : list B) (f : B -> C) (P : A -> C -> Prop),
  0 <= lo + offset <= hi + offset /\ hi + offset <= Zlength l' ->
  range_bin lo hi offset l (map f l') P ->
  range_bin lo hi offset l l' (fun x y => P x (f y)).
Proof.
  unfold range_bin, rangei. intros.
  fapply (H0 i ltac:(omega)).
  eq_solve with (rewrite Znth_map by omega).
Qed.

Lemma range_binB_Zrepeat : forall {A : Type} {da : Inhabitant A} {B : Type} {db : Inhabitant B}
  (lo hi n offset : Z) (l : list A) (x : B) (P : A -> B -> Prop),
  0 <= lo + offset < hi + offset /\ hi + offset <= n ->
  range_bin lo hi offset l (Zrepeat n x) P ->
  range_uni lo hi l (fun y => P y x).
Proof.
  unfold range_bin, range_uni. intros.
  eapply rangei_shift'. 3 : exact H0.
  + omega.
  + unfold rangei. intros. eq_solve with Znth_solve.
Qed.

(************* range_form *********************)

Ltac apply_in lem H :=
  apply lem in H.

Ltac apply_in_hyps' lem :=
  repeat match goal with
  | H : ?T |- _ => apply lem in H; let n := numgoals in guard n = 1
  end.

Tactic Notation "apply_in_hyps" uconstr(lem) := apply_in_hyps' lem.

Ltac apply_in_hyps_with_Zlength_solve lem :=
  repeat match goal with
  | H : _ |- _ => apply -> lem in H; [idtac | Zlength_solve ..]
  end.

Ltac apply_in_hyps_with_Zlength_solve_destruct lem :=
repeat match goal with
| H : _ |- _ => apply -> lem in H; [destruct H | Zlength_solve ..]
end.


Lemma not_In_range_uni_iff : forall {A : Type} {d : Inhabitant A} (x : A) (l : list A),
  ~ In x l <-> range_uni 0 (Zlength l) l (fun e => e <> x).
Proof.
  unfold range_uni, rangei. intros; split; intros.
  - intro. apply H. subst x. apply Znth_In. auto.
  - intro. induction l; auto.
    inversion H0.
    + subst a. apply H with 0. list_solve.
      autorewrite with sublist. auto.
    + apply IHl; auto. intros.
        specialize (H (i+1) ltac:(list_solve)). autorewrite with list_form_rewrite Znth in *.
        fassumption.
Qed.

Lemma not_In_range_uni : forall {A : Type} {d : Inhabitant A} (x : A) (l : list A),
  ~ In x l -> range_uni 0 (Zlength l) l (fun e => e <> x).
Proof. intros. apply not_In_range_uni_iff. auto. Qed.

Lemma eq_range_bin_no_offset : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth i l2) ->
  range_bin lo hi 0 l1 l2 eq.
Proof. unfold range_bin, rangei. intros. replace (i + 0) with i by omega. auto. Qed.

Lemma eq_range_bin_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth (i + offset) l2) ->
  range_bin lo hi offset l1 l2 eq.
Proof. unfold range_bin, rangei. auto. Qed.

Lemma eq_range_bin_left_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth (offset + i) l2) ->
  range_bin lo hi offset l1 l2 eq.
Proof. unfold range_bin, rangei. intros. replace (i + offset) with (offset + i) by omega. auto. Qed.

Lemma eq_range_bin_minus_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth i l1 = Znth (i - offset) l2) ->
  range_bin lo hi (-offset) l1 l2 eq.
Proof. unfold range_bin, rangei. intros. replace (i + - offset) with (i - offset) by omega. auto. Qed.

Lemma eq_range_bin_reverse : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth (i + offset) l1 = Znth i l2) ->
  range_bin (lo + offset) (hi + offset) (-offset) l1 l2 eq.
Proof. unfold range_bin, rangei. intros. fapply (H (i - offset) ltac:(omega)). eq_solve. Qed.

Lemma eq_range_bin_reverse_left_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth (offset + i) l1 = Znth i l2) ->
  range_bin (lo + offset) (hi + offset) (-offset) l1 l2 eq.
Proof. unfold range_bin, rangei. intros. fapply (H (i - offset) ltac:(omega)). eq_solve. Qed.

Lemma eq_range_bin_reverse_minus_offset : forall {A : Type} {d : Inhabitant A} (lo hi offset : Z) (l1 l2 : list A),
  (forall i, lo <= i < hi -> Znth (i - offset) l1 = Znth i l2) ->
  range_bin (lo - offset) (hi - offset) offset l1 l2 eq.
Proof. unfold range_bin, rangei. intros. fapply (H (i + offset) ltac:(omega)). eq_solve. Qed.

Lemma In_Znth_iff : forall {A : Type} {d : Inhabitant A} (l : list A) (x : A),
  In x l <-> exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  intros. split; intro.
  - induction l; inversion H.
    + exists 0. list_solve2.
    + specialize (IHl H0). destruct IHl as [i []].
      exists (i + 1). list_solve2.
  - destruct H as [i []]. subst x. apply Znth_In. auto.
Qed.

Ltac rewrite_In_Znth_iff :=
  repeat match goal with
  | H : In ?x ?l |- _ =>
    rewrite In_Znth_iff in H;
    destruct H as [? []]
  end.

Ltac range_form :=
  apply_in_hyps not_In_range_uni;
  apply_in_hyps eq_range_bin_no_offset;
  apply_in_hyps eq_range_bin_offset;
  apply_in_hyps eq_range_bin_left_offset;
  apply_in_hyps eq_range_bin_minus_offset;
  apply_in_hyps eq_range_bin_reverse;
  apply_in_hyps eq_range_bin_reverse_left_offset;
  apply_in_hyps eq_range_bin_reverse_minus_offset;
  rewrite_In_Znth_iff.

(**************** range tactics **************************)
Ltac range_rewrite :=
  apply_in_hyps_with_Zlength_solve range_uni_app1;
  apply_in_hyps_with_Zlength_solve range_uni_app2;
  apply_in_hyps_with_Zlength_solve_destruct range_uni_app;
  apply_in_hyps_with_Zlength_solve range_uni_sublist;
  apply_in_hyps_with_Zlength_solve range_uni_map;
  apply_in_hyps_with_Zlength_solve range_uni_Zrepeat;
  apply_in_hyps_with_Zlength_solve range_uni_empty;
  apply_in_hyps_with_Zlength_solve range_binA_app1;
  apply_in_hyps_with_Zlength_solve range_binA_app2;
  apply_in_hyps_with_Zlength_solve_destruct range_binA_app;
  apply_in_hyps_with_Zlength_solve range_binA_sublist;
  apply_in_hyps_with_Zlength_solve range_binA_map;
  apply_in_hyps_with_Zlength_solve range_binA_Zrepeat;
  apply_in_hyps_with_Zlength_solve range_binB_app1;
  apply_in_hyps_with_Zlength_solve range_binB_app2;
  apply_in_hyps_with_Zlength_solve_destruct range_binB_app;
  apply_in_hyps_with_Zlength_solve range_binB_sublist;
  apply_in_hyps_with_Zlength_solve range_binB_map;
  apply_in_hyps_with_Zlength_solve range_binB_Zrepeat;
  apply_in_hyps_with_Zlength_solve range_bin_empty.

Lemma range_le_lt_dec : forall lo i hi,
  (lo <= i < hi) + ~(lo <= i < hi).
Proof.
  intros.
  destruct (Z_lt_le_dec i lo); destruct (Z_lt_le_dec i hi); left + right; omega.
Qed.

Ltac destruct_range i lo hi :=
  destruct (range_le_lt_dec lo i hi).

Ltac pose_new_res i lo hi H res :=
  assert_fails (assert res by assumption);
  destruct_range i lo hi;
  [ (tryif exfalso; omega then gfail else idtac);
    assert res by apply (H i ltac:(omega))
  | try omega
  ].

Definition range_saturate_shift {A : Type} (l : list A) (s : Z) :=
  True.

Lemma range_saturate_shift_pose : forall {A : Type} (l : list A) (s : Z),
  range_saturate_shift l s.
Proof. intros. apply I. Qed.

Ltac range_saturate_check_non_zero_loop_core1 :=
  repeat lazymatch goal with
  | H : range_saturate_shift ?l1 ?s1,
    H1 : range_bin ?lo ?hi ?s ?l1 ?l2 ?P |- _ =>
    lazymatch goal with
    | H2 : range_saturate_shift l2 ?s2 |- _ =>
      tryif assert (s1 + s = s2) by Zlength_solve
      then idtac
      else fail 1
    | |- _ =>
      pose (range_saturate_shift_pose l2 (s + s1))
    end;
    clear H1
  | H : range_saturate_shift ?l2 ?s2,
    H1 : range_bin ?lo ?hi ?s ?l1 ?l2 ?P |- _ =>
    pose (range_saturate_shift_pose l1 (s2 - s));
    clear H1
  end.

Ltac range_saturate_check_non_zero_loop_core :=
  repeat lazymatch goal with
  | H : range_bin ?lo ?hi ?s ?l1 ?l2 ?P |- _ =>
    pose (range_saturate_shift_pose l1 0);
    tryif range_saturate_check_non_zero_loop_core1
    then idtac
    else fail 1
  end.

Ltac range_saturate_check_non_zero_loop :=
  tryif (try (range_saturate_check_non_zero_loop_core; fail 1))
  then fail "The goal has non-zero loop"
  else idtac.

Ltac range_saturate :=
  repeat match goal with
  | H : range_uni ?lo ?hi ?l ?P |- _ =>
    match goal with
    | _ : context [Znth ?i l] |- _ =>
      let res := eval cbv beta in (P (Znth i l)) in
      pose_new_res i lo hi H res
    | |- context [Znth ?i l] =>
      let res := eval cbv beta in (P (Znth i l)) in
      pose_new_res i lo hi H res
    end
  | H : range_bin ?lo ?hi ?offset ?l1 ?l2 ?P |- _ =>
    match goal with
    | _ : context [Znth ?i l1] |- _ =>
      let res := eval cbv beta in (P (Znth i l1) (Znth (i + offset) l2)) in
      pose_new_res i lo hi H res
    | |- context [Znth ?i l1] =>
      let res := eval cbv beta in (P (Znth i l1) (Znth (i + offset) l2)) in
      pose_new_res i lo hi H res
    | _ : context [Znth ?i l2] |- _ =>
      let res := eval cbv beta in (P (Znth (i - offset) l1) (Znth i l2)) in
      pose_new_res (i - offset) lo hi H res
    | |- context [Znth ?i l2] =>
      let res := eval cbv beta in (P (Znth (i - offset) l1) (Znth i l2)) in
      pose_new_res (i - offset) lo hi H res
    end
  end.

Ltac range_saturate_full :=
  repeat match goal with
  | H : range_uni ?lo ?hi ?l ?P |- _ =>
    (let res := eval cbv beta in (P (Znth lo l)) in
     pose_new_res lo lo hi H res);
    (let res := eval cbv beta in (P (Znth (hi - 1) l)) in
     pose_new_res (hi-1) lo hi H res);
    match goal with
    | _ : context [Znth ?i l] |- _ =>
      let res := eval cbv beta in (P (Znth i l)) in
      pose_new_res i lo hi H res
    | |- context [Znth ?i l] =>
      let res := eval cbv beta in (P (Znth i l)) in
      pose_new_res i lo hi H res
    end
  | H : range_bin ?lo ?hi ?offset ?l1 ?l2 ?P |- _ =>
    first
    [ let res := eval cbv beta in (P (Znth lo l1) (Znth (lo + offset) l2)) in
      pose_new_res lo lo hi H res
    | let res := eval cbv beta in (P (Znth (hi - 1) l1) (Znth (hi - 1 + offset) l2)) in
      pose_new_res (hi-1) lo hi H res
    | match goal with
      | _ : context [Znth ?i l1] |- _ =>
        let res := eval cbv beta in (P (Znth i l1) (Znth (i + offset) l2)) in
        pose_new_res i lo hi H res
      | |- context [Znth ?i l1] =>
        let res := eval cbv beta in (P (Znth i l1) (Znth (i + offset) l2)) in
        pose_new_res i lo hi H res
      | _ : context [Znth ?i l2] |- _ =>
        let res := eval cbv beta in (P (Znth (i - offset) l1) (Znth i l2)) in
        pose_new_res (i - offset) lo hi H res
      | |- context [Znth ?i l2] =>
        let res := eval cbv beta in (P (Znth (i - offset) l1) (Znth i l2)) in
        pose_new_res (i - offset) lo hi H res
      end
    ]
  end.

Ltac list_prop_solve :=
  list_form; range_form; range_rewrite; Znth_solve2;
  range_saturate_check_non_zero_loop; range_saturate_full; Znth_solve2;
  auto with Znth_solve_hint;
  try fassumption;
  fail "list_prop_solve cannot solve this goal".

Create HintDb list_solve_unfold.

Ltac list_solve_preprocess :=
  fold_Vbyte;
  autounfold with list_solve_unfold;
  simpl data_at;
  repeat match goal with [ |- _ /\ _ ] => split end;
  intros.

Tactic Notation "list_solve!" :=
  list_solve_preprocess;
  solve
  [ Zlength_solve
  | list_solve2
  | list_prop_solve
  ].

(***************** Zlength_solve using a database *************)
Definition Zlength_tag := True.

Lemma Zlength_db_new : forall (H : Prop), H -> Zlength_tag /\ H.
Proof. unfold Zlength_tag. tauto. Qed.

Lemma Zlength_db_inc : forall (H H0 : Prop), H -> Zlength_tag /\ H0 -> Zlength_tag /\ (H /\ H0).
Proof. tauto. Qed.

Ltac add_Zlength_res H :=
  first
  [ match goal with res_db : Zlength_tag /\ ?res |- _ =>
      let new_db := fresh in
      pose (Zlength_db_inc _ _ H res_db) as new_db;
      clearbody new_db;
      clear res_db;
      rename new_db into res_db
    end
  | let new_db := fresh "Zlength_db" in
    pose (Zlength_db_new _ H) as new_db;
    clearbody new_db
  ].

Ltac search_Zlength l :=
  match goal with res_db : Zlength_tag /\ ?res |- _ =>
    let rec search_aux res :=
      match res with
      | ?res1 /\ ?res2 => first [search_aux res1 | search_aux res2]
      | Zlength l = _ => idtac
      end
    in
    search_aux res
  end.

Ltac calc_Zlength l :=
  first
  [ search_Zlength l
  | lazymatch l with
    | ?l1 ++ ?l2 =>
      calc_Zlength l1; calc_Zlength l2;
      add_Zlength_res (Zlength_app _ l1 l2)
    | Zrepeat ?n ?x =>
      add_Zlength_res (Zlength_Zrepeat _ n x ltac:(omega))
    | map _ _ ?f ?l =>
      add_Zlength_res (Zlength_map _ _ f l)
    | _ => fail "calc_Zlength does not support" l
    end
  ].


(*************** list_deduce experiment *************)
(* This experiment is replaced by Znth_solve *)
(*
Lemma sublist_Zrepeat : forall (A : Type) (lo hi n : Z) (x : A),
  0 <= lo <= hi -> hi <= n ->
  sublist lo hi (Zrepeat n x) = Zrepeat (hi - lo) x.
Proof. intros. apply sublist_list_repeat; omega. Qed.

Lemma map_Zrepeat : forall (A B : Type) (f : A -> B) (n : Z) (x : A),
  map f (Zrepeat n x) = Zrepeat n (f x).
Proof. intros. apply map_list_repeat. Qed.

Hint Rewrite sublist_Zrepeat Znth_Zrepeat using Zlength_solve : sublist2.
Hint Rewrite map_Zrepeat @map_sublist map_app : sublist2.
Hint Rewrite sublist_app1 @sublist_app2 @sublist_app' using Zlength_solve : sublist2.
Hint Rewrite app_nil_l app_nil_r : sublist2.
Hint Rewrite <- app_assoc : sublist2.

Ltac list_normalize :=
  list_form; autorewrite with sublist2.

Lemma list_split : forall (A : Type) (i : Z) (l : list A),
  0 <= i <= Zlength l ->
  l = sublist 0 i l ++ sublist i (Zlength l) l.
Proof.
  intros. rewrite <- sublist_same at 1 by auto. apply sublist_split; omega.
Qed.

Ltac list_deduce :=
  lazymatch goal with
  | |- @eq (list _) _ _ => idtac
  | |- _ => fail "list_deduce can only solve list equations"
  end;
  let A :=
    match goal with |- @eq (list ?A) _ _ => A end
  in
  lazymatch goal with
  | |- (?l1 ++ ?l2) = ?r => idtac
  | |- ?l = ?r =>
    rewrite <- (app_nil_r l) at 1
  end;
  lazymatch goal with
  | |- ?l = (?r1 ++ ?r2) => idtac
  | |- ?l = ?r =>
    symmetry; rewrite <- (app_nil_r r) at 1; symmetry
  end;
  let ltail := fresh in
  let rtail := fresh in
  lazymatch goal with
  | |- (?l1 ++ ?l2) = (?r1 ++ ?r2) =>
    pose (ltail := l2); pose (rtail := r2);
    change (l1 ++ ltail = r1 ++ rtail);
    let H := fresh in
    first
    [ assert (H : Zlength l1 = Zlength r1) by Zlength_solve
    | assert (H : Zlength l1 <= Zlength r1) by Zlength_solve;
      let left := fresh in
      pose (left := l1);
      change (left ++ ltail = r1 ++ rtail);
      rewrite (list_split A (Zlength l1) r1) by Zlength_solve;
      rewrite <- app_assoc;
      subst left
    | assert (H : Zlength l1 >= Zlength r1) by Zlength_solve;
      let right := fresh in
      pose (right := l1);
      change (l1 ++ ltail = right ++ rtail);
      rewrite (list_split A (Zlength r1) l1) by Zlength_solve;
      rewrite <- app_assoc;
      subst right
    ];
    clear H;
    subst ltail rtail;
    f_equal
  end;
  list_normalize.

Hint Rewrite @sublist_sublist using Zlength_solve : sublist2.
*)





