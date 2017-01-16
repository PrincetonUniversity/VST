Require Import floyd.proofauto. (* Import the Verifiable C system *)
Require Import progs.bin_search. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Fixpoint sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x::rest =>
    match rest with [] => True | y::_ =>  x <= y /\ sorted rest end
  end.

(* Beginning of the API spec for the bin_search.c program *)
Definition search_spec :=
 DECLARE _search
  WITH a: val, sh : share, contents : list Z, tgt : Z, lo : Z, hi : Z
  PRE [ _a OF (tptr tint), _tgt OF tint, _lo OF tint, _hi OF tint ]
            PROP  (readable_share sh; Zlength contents <= Int.max_signed;
                     0 <= lo <= Int.max_signed; Int.min_signed <= hi <= Int.max_signed / 2;
                     hi <= Zlength contents; sorted contents;
                     Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
                     Int.min_signed <= tgt <= Int.max_signed)
                  LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
                         temp _lo (Vint (Int.repr lo)); temp _hi (Vint (Int.repr hi)))
          SEP   (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX i:Z,
         PROP (if in_dec Z.eq_dec tgt (sublist lo hi contents) then Znth i contents 0 = tgt else i = -1)
          LOCAL (temp ret_temp  (Vint (Int.repr i)))
           SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [search_spec; main_spec]).

Lemma sublist_nil1 : forall A i j (l : list A), j <= i -> sublist i j l = [].
Proof.
  intros; destruct (eq_dec i j).
  - subst; apply sublist_nil.
  - unfold sublist; rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma Znth_In : forall A i (l : list A) d x (Hrange : 0 <= i < Zlength l)
                       (Hnth : Znth i l d = x), In x l.
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); [omega|].
  subst; apply nth_In.
  rewrite Zlength_correct in Hrange; auto; Omega0.
Qed.

Lemma In_Znth : forall A (l : list A) x d,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  unfold Znth; intros.
  apply In_nth with (d := d) in H; destruct H as (n & ? & ?).
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; omega.
  - destruct (zlt (Z.of_nat n) 0); [omega|].
    rewrite Nat2Z.id; auto.
Qed.

Lemma sublist_of_nil : forall A i j, sublist i j (nil : list A) = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_nil, firstn_nil; auto.
Qed.

Fixpoint sorted2 l :=
  match l with
  | [] => True
  | x :: rest => Forall (fun y => x <= y) rest /\ sorted2 rest
  end.

Lemma sorted_equiv : forall l, sorted l <-> sorted2 l.
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct l.
    + simpl; split; auto.
    + rewrite IHl; simpl; split; intros (? & Hall & ?).
      * split; auto; constructor; auto.
        rewrite Forall_forall in *; intros ? Hin.
        specialize (Hall _ Hin); omega.
      * inversion H; subst; auto.
Qed.

Lemma sorted_mono : forall d l i j (Hsort : sorted l) (Hi : 0 <= i <= j)
                           (Hj : j < Zlength l),
    Znth i l d <= Znth j l d.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  destruct (zlt j 0); [omega|].
  revert Hsort.
  generalize dependent j; generalize dependent i; induction l; simpl in *; intros.
  { rewrite Zlength_correct in *; simpl in *; omega. }
  destruct l.
  + rewrite Zlength_correct in *; simpl in *.
    assert (j = 0) by omega.
    assert (i = 0) by omega.
    subst; omega.
  + destruct (eq_dec j 0).
    { assert (i = 0) by omega.
      subst; omega. }
    destruct (Z.to_nat j) eqn: Hnj.
    { contradiction n; apply Z2Nat_inj_0; auto. }
    destruct (eq_dec i 0).
    * subst; simpl.
      destruct Hsort as (? & Hsort).
      destruct n0; try omega.
      rewrite sorted_equiv in Hsort; simpl in Hsort.
      destruct Hsort as (Hsort & _).
      assert (In (nth n0 l d) l) as Hin.
      { apply nth_In.
        assert (S (S n0) < length (a :: z :: l))%nat.
        { rewrite Z2Nat.inj_lt in Hj; try omega.
          rewrite Hnj, Zlength_correct, Nat2Z.id in Hj; auto. }
        simpl in *; omega. }
      rewrite Forall_forall in Hsort; specialize (Hsort _ Hin); omega.
    * destruct (Z.to_nat i) eqn: Hni.
      { contradiction n1; apply Z2Nat_inj_0; auto. }
      assert (Z.of_nat n2 >= 0) as Hi' by omega.
      specialize (IHl _ Hi' (Z.of_nat n0)).
      destruct Hsort.
      repeat rewrite Nat2Z.id in IHl; apply IHl; auto; try omega.
      - split; try omega.
        destruct Hi as (_ & Hi).
        rewrite Z2Nat.inj_le in Hi; omega.
      - rewrite Z2Nat.inj_lt in Hj; try omega.
        rewrite Hnj, Zlength_correct, Nat2Z.id in Hj.
        rewrite Zlength_correct; apply inj_lt; simpl in *; omega.
Qed.

Lemma In_sorted_range : forall d lo hi x l (Hsort : sorted l) (Hlo : 0 <= lo <= hi)
                              (Hhi : hi <= Zlength l)
                              (Hin : In x (sublist lo hi l)),
    Znth lo l d <= x <= Znth (hi - 1) l d.
Proof.
  intros.
  generalize (In_Znth _ _ _ d Hin); intros (i & Hrange & Hi).
  rewrite Zlength_sublist in Hrange; auto.
  rewrite Znth_sublist in Hi; auto; try omega.
  subst; split; apply sorted_mono; auto; omega.
Qed.

Lemma In_sorted_gt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l 0 = n)
                            (Hgt : n < x),
    In x (sublist (i + 1) hi l).
Proof.
  intros.
  rewrite sublist_split with (mid := i + 1) in Hin; try omega.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range 0 lo (i + 1) x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | omega]).
  replace (i + 1 - 1) with i in X by omega.
  specialize (X H); subst; omega.
Qed.

Lemma In_sorted_lt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l 0 = n)
                            (Hgt : x < n),
    In x (sublist lo i l).
Proof.
  intros.
  rewrite sublist_split with (mid := i) in Hin; try omega.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range 0 i hi x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | omega]).
  specialize (X H); subst; omega.
Qed.

Definition while_Inv contents tgt sh a lo hi := EX lo' : Z, EX hi' : Z,
    PROP  (readable_share sh; Zlength contents <= Int.max_signed;
           0 <= lo' <= Int.max_signed; Int.min_signed <= hi' <= Int.max_signed / 2;
           hi' <= Zlength contents;
           In tgt (sublist lo hi contents) <-> In tgt (sublist lo' hi' contents))
    LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
           temp _lo (Vint (Int.repr lo')); temp _hi (Vint (Int.repr hi')))
    SEP   (data_at sh (tarray tint (Zlength contents))
                   (map Vint (map Int.repr contents)) a).

Lemma entail_post : forall Delta P Post ek vl,
    ENTAIL Delta, P |-- Post EK_normal None ->
    ENTAIL Delta, overridePost P Post ek vl |-- Post ek vl.
Proof.
  intros.
  unfold overridePost; destruct (eq_dec ek EK_normal).
  - normalize; subst; auto.
  - unfold local, lift1; simpl; normalize.
Qed.

Lemma Zlength_sublist : forall A (l : list A) lo hi (Hhi : hi <= Zlength l)
  (Hlo : 0 <= lo <= hi),
  Zlength (sublist lo hi l) = hi - lo.
Proof.
  intros; unfold sublist.
  rewrite Zlength_correct, firstn_length, skipn_length.
  rewrite Min.min_l, Z2Nat.id; try omega.
  rewrite Zlength_correct, Z2Nat.inj_sub in *; Omega0.
Qed.

Lemma Znth_In_sublist : forall A i (l : list A) d lo hi
  (Hlo : 0 <= lo <= i) (Hhi : i < hi <= Zlength l),
  In (Znth i l d) (sublist lo hi l).
Proof.
  intros.
  apply Znth_In with (i := i - lo)(d := d).
  - rewrite Zlength_sublist; omega.
  - rewrite <- (Z.sub_simpl_r i lo) at 2.
    apply Znth_sublist; omega.
Qed.

Lemma sublist_In_sublist : forall A (l : list A) x lo hi lo' hi' (Hlo : 0 <= lo <= lo')
  (Hhi : hi' <= hi), In x (sublist lo' hi' l) -> In x (sublist lo hi l).
Proof.
  intros.
  apply sublist_In with (lo0 := lo' - lo)(hi0 := hi' - lo); rewrite sublist_sublist;
    try split; try omega.
  - repeat rewrite Z.sub_simpl_r; auto.
  - destruct (Z_le_dec hi' lo'); try omega.
    rewrite sublist_nil1 in *; auto; simpl in *; contradiction.
Qed.

Lemma body_search: semax_body Vprog Gprog f_search search_spec.
Proof.
  start_function.
  pose proof Int.min_signed_neg.
  forward_while (while_Inv contents tgt sh a lo hi).
  { unfold while_Inv.
    Exists lo; Exists hi; entailer. }
  { entailer!. }
  forward.
  rewrite Int.shr_div_two_p, Int.add_signed.
  repeat rewrite Int.signed_repr; try omega.
  rewrite Int.unsigned_repr; try computable; simpl.
  unfold two_power_pos; simpl.
  remember ((lo' + hi') / 2) as mid.
  assert (0 <= mid < Zlength (map Int.repr contents)).
  { subst; split; [apply Z_div_pos; try omega|].
    rewrite Zlength_map.
    apply Zdiv_lt_upper_bound; omega. }
  assert (0 <= mid < Zlength contents) by (rewrite Zlength_map in *; auto).
  assert (lo' <= (lo' + hi') / 2 < hi').
  { split; [apply Zdiv_le_lower_bound | apply Zdiv_lt_upper_bound]; omega. }
  forward.
  exploit Znth_In; eauto.
  instantiate (1 := 0); intro Hin.
  match goal with H : Forall _ _ |- _ =>
                  rewrite Forall_forall in H; specialize (H _ Hin) end.
(*Ltac forward_if_tac post :=
  check_Delta;
  repeat (apply -> seq_assoc; abbreviate_semax);
first [ignore (post: environ->mpred)
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
match goal with
 | |- semax _ _ (Sifthenelse _ _ _) (overridePost post _) =>
       forward_if'_new
 | |- semax _ _ (Sifthenelse _ _ _) ?P =>
      apply (semax_post_flipped (overridePost post P));
      [ forward_if'_new
      | try (intros; apply entail_post; simpl); try solve [normalize]
      ]
   | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
     apply semax_seq with post;
      [forward_if'_new | abbreviate_semax; autorewrite with ret_assert]
end.
check_Delta;
match goal with |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Sifthenelse ?e ?c1 ?c2) _ =>
   let HRE := fresh "H" in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R e v HRE;
    simpl in v;
    apply (semax_ifthenelse_PQR' _ v);
     [ reflexivity | entailer | assumption
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE;
       do_repr_inj HRE; abbreviate_semax
     | clear HRE; subst v; apply semax_extract_PROP; intro HRE;
       do_repr_inj HRE; abbreviate_semax
     ]
end.
forward_if_tac (while_Inv contents tgt sh a).
  Focus 3.
  intro; unfold while_Inv; normalize.
  simpl.
  unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift; simpl; normalize.
  Exists (x0, x1); entailer.*)
  forward_if.
  - forward.
    Exists ((lo' + hi') / 2); entailer!.
    destruct (in_dec _ _ _); auto.
    subst; contradiction n.
    match goal with H : _ <-> _ |- _ => rewrite H end.
    apply Znth_In_sublist; omega.
  - forward_if.
    + forward.
      Exists ((mid + 1), hi'); entailer!.
      match goal with H : _ <-> _ |- _ => rewrite H end.
      split; intro Hin'.
      * eapply In_sorted_gt; eauto; omega.
      * eapply sublist_In_sublist; try apply Hin'; omega.
    + forward.
      Exists (lo', mid); entailer!.
      match goal with H : _ <-> _ |- _ => rewrite H end.
      split; intro Hin'.
      * eapply In_sorted_lt; eauto; omega.
      * eapply sublist_In_sublist; try apply Hin'; omega.
(*  - intros.

    unfold while_Inv.

    intros; unfold POSTCONDITION, abbreviate, overridePost.
    destruct ek; entailer!.
    unfold overri
    intros.
    unfold exit_tycon.

    unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift; simpl; entailer!.
    unfold overridePost; destruct (eq_dec ek EK_normal); auto.
    subst; simpl; normalize.
    unfold while_Inv.
    (* For some reason, Intro doesn't work here. *)
    refine (exp_left _ _ _); intro lo1.
    refine (exp_left _ _ _); intro hi1.
    Exists (lo1, hi1).
    normalize.*)
  - split; try omega.
    etransitivity; [apply (Zplus_le_compat_l _ (Int.max_signed / 2)); omega|].
    etransitivity; [apply (Zplus_le_compat_r _ (Int.max_signed / 2)); omega|].
    rewrite Zplus_diag_eq_mult_2, Z.mul_comm.
    apply Z_mult_div_ge; omega.
  - forward.
    Exists (-1); entailer!.
    destruct (in_dec _ _ _); auto.
    match goal with H : _ <-> _ |- _ => rewrite H in i end.
    rewrite sublist_nil1 in i; [|omega].
    simpl in i; contradiction.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name four _four.
  start_function.
  forward_call (four,Ews,four_contents,3,0,4).
  { split; auto; simpl.
    repeat split; try omega; try computable.
    * unfold four_contents, Zlength; simpl; computable.
    * unfold four_contents, Zlength; simpl; computable.
    * repeat constructor; computable. }
  Intro r; forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_cons body_search.
semax_func_cons body_main.
Qed.
