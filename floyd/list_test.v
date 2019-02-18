Require Import VST.floyd.proofauto.
Require Import Coq.Program.Tactics.

Example strcat_preloop2 : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  intros.
  list_form.
  apply data_subsume_array_ext; only 1, 2 : Zlength_solve.
  intros. Znth_solve; auto.
Qed.

Lemma split_data_at_app_tschar:
 forall {cs : compspecs} sh n (al bl: list val) p ,
   n = Zlength (al++bl) ->
   data_at sh (tarray tschar n) (al++bl) p = 
         data_at sh (tarray tschar (Zlength al)) al p
        * data_at sh (tarray tschar (n - Zlength al)) bl
                 (field_address0 (tarray tschar n) [ArraySubsc (Zlength al)] p).
Proof.
intros.
apply (split2_data_at_Tarray_app _ n  sh tschar al bl ); auto.
rewrite Zlength_app in H.
change ( Zlength bl = n - Zlength al); omega.
Qed.

Example strcat_preloop2_old : forall {cs : compspecs} n ld,
  n > Zlength ld ->
  data_subsume (tarray tschar n)
    (map Vbyte (ld ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + 1))) Vundef)
    (map Vbyte ld ++ list_repeat (Z.to_nat (n - Zlength ld)) Vundef).
Proof.
  unfold data_subsume; intros.
  autorewrite with sublist.
  rewrite !map_app. rewrite <- app_assoc.
  rewrite split_data_at_app_tschar by list_solve.
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  autorewrite with sublist.
  cancel.
Qed.

Example strcat_retutn : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros.
  list_form.
  eapply Znth_eq_ext; only 1 : Zlength_solve.
  autorewrite with Zlength. intros. Znth_solve; auto.
Qed.

Example strcat_retutn_alt : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros. list_normalize. repeat list_deduce. f_equal. Zlength_solve.
Qed.

Example strcat_return_old : forall n (ld ls : list byte),
  Zlength ld + Zlength ls < n ->
  map Vbyte (ld ++ ls) ++
  upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls))) Vundef) (Vint (Int.repr (Byte.signed (Znth 0 [Byte.zero])))) =
  map Vbyte ((ld ++ ls) ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ld + Zlength ls + 1))) Vundef.
Proof.
  intros.
  replace (n - (Zlength ld + Zlength ls))
    with (1 + (n - (Zlength ld + Zlength ls+1))) by rep_omega.
  rewrite <- list_repeat_app' by rep_omega.
  rewrite upd_Znth_app1 by list_solve.
  rewrite app_assoc.
  simpl.
  rewrite !map_app.
  reflexivity.
Qed.

Example strcat_loop2 : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros.
  apply derives_refl'. f_equal.
  eapply Znth_eq_ext; only 1 : Zlength_solve.
  autorewrite with Zlength. intros. list_form. Znth_solve.
  fold_Vbyte. do 2 f_equal. omega.
Qed.

Example strcat_loop2_alt : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros.
  apply data_subsume_array_ext; only 1,2 : Zlength_solve.
  intros. list_form. unfold data_subsume; intros; Znth_solve.
  fold_Vbyte.
  auto with cancel Zlength_solve f_equal.
Qed.

Example strcat_loop2_old : forall {cs : compspecs} sh n x ld ls dest,
  Zlength ls + Zlength ld < n ->
  0 <= x < Zlength ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (ld ++ sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - (Zlength ld + x))) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ld ++ sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (Zlength ld + (x + 1)))) Vundef)
      dest.
Proof.
  intros. rename x into j.
  rewrite (sublist_split 0 j (j+1)) by rep_omega.
  rewrite (app_assoc ld). rewrite !map_app.
  rewrite <- (app_assoc (_ ++ _)).
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  rewrite (split_data_at_app_tschar _ n) by list_solve.
  replace (n - (Zlength ld + j))
    with (1 + (n - (Zlength ld + (j + 1)))) by rep_omega.
  rewrite <- list_repeat_app' by rep_omega.
  cancel.
  rewrite upd_Znth_app1 by (autorewrite with sublist; rep_omega).
  rewrite app_Znth1 by list_solve.
  rewrite sublist_len_1 by rep_omega.
  cancel.
Qed.

Example strcpy_return : forall {cs : compspecs} sh n ls dest,
  Zlength ls < n ->
  data_at sh (tarray tschar n)
  (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero)))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) dest.
Proof.
  intros.
  list_form.
  apply data_subsume_array_ext. Zlength_solve. Zlength_solve.
  autorewrite with Zlength. intros. Znth_solve.
Qed.

Example strcpy_return_old : forall {cs : compspecs} sh n ls dest,
  Zlength ls < n ->
  data_at sh (tarray tschar n)
  (map Vbyte ls ++ upd_Znth 0 (list_repeat (Z.to_nat (n - Zlength ls)) Vundef) (Vint (Int.repr (Byte.signed Byte.zero)))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (ls ++ [Byte.zero]) ++ list_repeat (Z.to_nat (n - (Zlength ls + 1))) Vundef) dest.
Proof.
  intros.
  autorewrite with sublist.
  rewrite !map_app.
  rewrite <- app_assoc.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   rewrite (split_data_at_app_tschar _ n) by list_solve.
   autorewrite with sublist.
   replace (n - Zlength ls) with (1 + (n - (Zlength ls + 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  autorewrite with sublist.
  rewrite !split_data_at_app_tschar by list_solve.
  cancel.
Qed.

Example strcpy_loop : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  ~ In Byte.zero ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.
Proof.
  intros.
  list_form. assert (x < Zlength ls) by cstring.
  apply derives_refl'.
  f_equal. apply Znth_eq_ext. Zlength_solve.
  autorewrite with Zlength. intros. Znth_solve. fold_Vbyte.
  do 2 f_equal. omega.
Qed.

Ltac Znth_solve2 :=
  autorewrite with Zlength in *; autorewrite with Znth_solve in *; auto; try congruence; (* try solve [exfalso; auto]; *)
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

Ltac Zlength_solve ::= autorewrite with Zlength; pose_Zlength_nonneg; omega.

Ltac list_form ::=
  autorewrite with list_form in *.
Hint Rewrite app_nil_r : list_form.

Example strcpy_loop_new : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.
Proof.
  intros. list_form.
  apply derives_refl'.
  f_equal. apply Znth_eq_ext. Znth_solve2. Zlength_solve.
  intros. Znth_solve2.
  fold_Vbyte. do 2 f_equal. omega.
Qed.

Example strcpy_loop_old : forall {cs : compspecs} sh n x ls dest,
  Zlength ls < n ->
  0 <= x < Zlength ls + 1 ->
  Znth x (ls ++ [Byte.zero]) <> Byte.zero ->
  ~ In Byte.zero ls ->
  data_at sh (tarray tschar n)
  (map Vbyte (sublist 0 x ls) ++
   upd_Znth 0 (list_repeat (Z.to_nat (n - x)) Vundef) (Vint (Int.repr (Byte.signed (Znth x (ls ++ [Byte.zero])))))) dest
|-- data_at sh (tarray tschar n) (map Vbyte (sublist 0 (x + 1) ls) ++ list_repeat (Z.to_nat (n - (x + 1))) Vundef) dest.
Proof.
  intros. rename x into i.
  assert (i < Zlength ls) by cstring.
  rewrite (sublist_split 0 i (i+1)) by list_solve.
  rewrite !map_app. rewrite <- app_assoc.
  autorewrite with sublist.
  rewrite !(split_data_at_app_tschar _ n) by list_solve.
  autorewrite with sublist.
   replace (n - i) with (1 + (n-(i+ 1))) at 2 by list_solve.
  rewrite <- list_repeat_app' by omega.
  autorewrite with sublist.
  cancel.
  rewrite !split_data_at_app_tschar by list_solve.
  autorewrite with sublist.
  rewrite sublist_len_1 by omega.
  simpl. cancel.
Qed.


Lemma imp_refl' : forall P Q : Prop,
  P = Q -> P -> Q.
Proof. intros. congruence. Qed.

Ltac fapply H :=
  match type of H with ?HH =>
  eapply (imp_refl' HH); only 2 : assumption; repeat f_equal
  end.

Lemma not_In_forall : forall {A : Type} {d : Inhabitant A} (x : A) (l : list A),
  ~ In x l <-> forall i, 0 <= i < Zlength l -> Znth i l <> x.
Proof.
  intros; split; intros.
  - intro. apply H. subst x. apply Znth_In. auto.
  - intro. induction l; auto.
    inversion H0.
    + subst a. apply H with 0. list_solve.
      autorewrite with sublist. auto.
    + apply IHl; auto. intros.
        specialize (H (i+1) ltac:(list_solve)). autorewrite with list_form Znth_solve in *.
        fapply H. Zlength_solve.
Qed.

Lemma range_le_lt_dec : forall lo i hi,
  (lo <= i < hi) + ~(lo <= i < hi).
Proof.
  intros.
  Search ((_ <= _)%Z + (_ < _)%Z).
  destruct (Z_lt_le_dec i lo); destruct (Z_lt_le_dec i hi); left + right; omega.
Qed.

Ltac destruct_range Hrange :=
  let Hrange := eval simpl in Hrange in
  lazymatch Hrange with
  | ?lo <= ?i < ?hi =>
    destruct (range_le_lt_dec lo i hi)
  end.

Ltac fassumption :=
  first
  [ assumption
  | match goal with
    | H : _ |- _ => fapply H; match goal with |- (_ = _)%Z => idtac end; Zlength_solve
    end
  ].

Definition range_uni {A : Type} {d : Inhabitant A} (lo hi : Z) (l : list A) (P : A -> Prop) :=
  forall i, lo <= i < hi -> P (Znth i l).

Definition range_bin {A : Type} {dA : Inhabitant A} {B : Type} {dB : Inhabitant B}
  (lo hi offset : Z) (al : list A) (bl : list B) (P : A -> B -> Prop) :=
  forall i, lo <= i < hi -> P (Znth i al) (Znth (i+offset) bl).

Lemma range_uni_app1 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= hi /\ hi <= Zlength al ->
  range_uni lo hi (al ++ bl) P ->
  range_uni lo hi al P.
Proof.
  unfold range_uni. intros. specialize (H0 i). autorewrite with Znth_solve in H0. auto.
Qed.

Lemma range_uni_app2 : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  Zlength al <= lo <= hi /\ hi <= Zlength al + Zlength bl ->
  range_uni lo hi (al ++ bl) P ->
  range_uni (lo - Zlength al) (hi - Zlength al) bl P.
Proof.
  unfold range_uni. intros. specialize (H0 (i + Zlength al) ltac:(omega)).
  autorewrite with Znth_solve in H0. fapply H0. omega.
Qed.

Lemma range_uni_app : forall {A : Type} {d : Inhabitant A} (lo hi : Z) (al bl : list A) (P : A -> Prop),
  0 <= lo <= Zlength al /\ Zlength al <= hi <= Zlength bl ->
  range_uni lo hi (al ++ bl) P ->
  range_uni lo (Zlength al) al P /\
  range_uni 0 (hi - Zlength al) bl P.
Proof.
  unfold range_uni. intros. split; intros.
  - specialize (H0 i ltac:(omega)). autorewrite with Znth_solve in H0. apply H0.
  - specialize (H0 (i + Zlength al) ltac:(omega)). autorewrite with Znth_solve in H0. fapply H0. omega.
Qed.

Ltac Znth_saturate :=
  repeat match goal with
  H : range_uni ?lo ?hi ?l ?P |- _ =>
    match goal with
    | _ : context [Znth ?i l] |- _ =>
      let res := eval cbv beta in (P (Znth i l)) in
      assert_fails (assert res by assumption);
      assert res by (apply H; Zlength_solve)
    end
  end;
  repeat match goal with
  H : forall i : Z, ?Hrange -> Znth i ?l1 = Znth i ?l2 |- _ =>
    match goal with
    | _ : context [Znth ?i l1] |- _ =>
    assert_fails (assert (Znth i l1 = Znth i l2) by assumption);
      first
      [ assert (Znth i l1 = Znth i l2) by (apply H; Zlength_solve)
      | assert_fails (assert (~(fun i => Hrange) i) by Zlength_solve);
        destruct_range ((fun i => Hrange) i); try assert (Znth i l1 = Znth i l2) by (apply H; Zlength_solve)
      ]
    | |- context [Znth ?i l1] =>
    assert_fails (assert (Znth i l1 = Znth i l2) by assumption);
      first
      [ assert (Znth i l1 = Znth i l2) by (apply H; Zlength_solve)
      | assert_fails (assert (~(fun i => Hrange) i) by Zlength_solve);
        destruct_range ((fun i => Hrange) i); try assert (Znth i l1 = Znth i l2) by (apply H; Zlength_solve)
      ]
    end
  end.

Lemma not_In_range_uni : forall {A : Type} {d : Inhabitant A} (x : A) (l : list A),
  ~ In x l ->
  range_uni 0 (Zlength l) l (fun e => e <> x).
Proof.
  intros. rewrite @not_In_forall in *. unfold range_uni. apply H.
Qed.

Ltac apply_in lem H :=
  apply lem in H.

Ltac apply_in_hyps' lem :=
  repeat match goal with
  | H : ?T |- _ => apply lem in H; let n := numgoals in guard n = 1
  end.

Tactic Notation "apply_in_hyps" uconstr(lem) := apply_in_hyps' lem.

(* This is a very hard case, a lot of deductions are needed *)
(* cool automation now! *)
Example strcmp_loop_new : forall i ls1 ls2,
  ~ In Byte.zero ls1 ->
  ~ In Byte.zero ls2 ->
  0 <= i < Zlength ls1 + 1 ->
  0 <= i < Zlength ls2 + 1 ->
  (forall j : Z, 0 <= j < i -> Znth j ls1 = Znth j ls2) ->
  i <> Zlength ls1 \/ i <> Zlength ls2 ->
  Znth i (ls1 ++ [Byte.zero]) = Znth i (ls2 ++ [Byte.zero]) ->
  i + 1 < Zlength ls1 + 1 /\
  i + 1 < Zlength ls2 + 1 /\
  forall j : Z, 0 <= j < i + 1 -> Znth j ls1 = Znth j ls2.
Proof.
  intros.
  list_form. apply_in_hyps not_In_range_uni.
  Time split3; intros; Znth_solve2; try omega; Znth_saturate; try congruence; fassumption.
  (* Finished transaction in 1.383 secs (1.375u,0.s) (successful) *)
Qed.

Example strcmp_loop_old : forall i ls1 ls2,
  ~ In Byte.zero ls1 ->
  ~ In Byte.zero ls2 ->
  0 <= i < Zlength ls1 + 1 ->
  0 <= i < Zlength ls2 + 1 ->
  sublist 0 i ls1 = sublist 0 i ls2 ->
  i <> Zlength ls1 \/ i <> Zlength ls2 ->
  Znth i (ls1 ++ [Byte.zero]) = Znth i (ls2 ++ [Byte.zero]) ->
  (Znth i (ls1 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls1) -> (* these two are not needed as they can be derived *)
  (Znth i (ls2 ++ [Byte.zero]) = Byte.zero <-> i = Zlength ls2) -> (* it makes proof easier to put them here *)
  i + 1 < Zlength ls1 + 1 /\
  i + 1 < Zlength ls2 + 1 /\
  sublist 0 (i+1) ls1 = sublist 0 (i+1) ls2.
Proof.
  intros.
  destruct (zlt i (Zlength ls1)).
  2:{
         assert (i = Zlength ls1) by omega. subst.
         destruct H4; [congruence | ].
         assert (Zlength ls1 < Zlength ls2) by omega.
         rewrite app_Znth2 in H5 by rep_omega.
         rewrite app_Znth1 in H5 by rep_omega.
         rewrite Z.sub_diag in H5. contradiction H0.
         change (Znth 0 [Byte.zero]) with Byte.zero in H5.
         rewrite H5. apply Znth_In. omega.
   }
  destruct (zlt i (Zlength ls2)).
  2:{
         assert (i = Zlength ls2) by omega. subst.
         destruct H4; [ | congruence].
         assert (Zlength ls1 > Zlength ls2) by omega.
         rewrite app_Znth1 in H5 by rep_omega.
         rewrite app_Znth2 in H5 by rep_omega.
         rewrite Z.sub_diag in H5. contradiction H.
         change (Znth 0 [Byte.zero]) with Byte.zero in H5.
         rewrite <- H5.  apply Znth_In. omega.
   }
  rewrite (sublist_split 0 i (i+1)) by omega.
  rewrite (sublist_split 0 i (i+1)) by omega.
  f_equal; auto.
  rewrite !sublist_len_1 by omega.
  autorewrite with sublist in H5.
  split. rep_omega. split. rep_omega.
  f_equal; auto. f_equal. auto.
Qed.


