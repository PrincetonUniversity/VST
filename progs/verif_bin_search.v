Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.progs.bin_search. (* Import the AST of this C program *)
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
            PROP  (readable_share sh;
                     0 <= lo <= Int.max_signed; 
                     hi <= Zlength contents <= Int.max_signed;
                     Int.min_signed <= hi <= Int.max_signed / 2;
                     sorted contents;
                     Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
                     Int.min_signed <= tgt <= Int.max_signed)
                  LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
                         temp _lo (Vint (Int.repr lo)); temp _hi (Vint (Int.repr hi)))
          SEP   (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX i:Z,
         PROP (if in_dec Z.eq_dec tgt (sublist lo hi contents) then Znth i contents = tgt else i = -1)
          LOCAL (temp ret_temp  (Vint (Int.repr i)))
           SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [search_spec; main_spec]).

Lemma sublist_nil1 : forall A i j (l : list A), j <= i -> sublist i j l = [].
Proof.
  intros; destruct (eq_dec i j).
  - subst; apply sublist_nil.
  - unfold sublist; rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma Znth_In : forall A (d: Inhabitant A) i (l : list A) x (Hrange : 0 <= i < Zlength l)
                       (Hnth : Znth i l = x), In x l.
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); [omega|].
  subst; apply nth_In.
  rewrite Zlength_correct in Hrange; auto.
  rep_omega.
Qed.

Lemma In_Znth : forall A (d: Inhabitant A) (l : list A) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l = x.
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
    + rewrite IHl; simpl; split; intros (? & Hall & ?); split3; auto.
       * constructor; auto.
          rewrite Forall_forall in *; intros ? Hin.
          specialize (Hall _ Hin); omega.
       * inversion H. auto.
Qed.

Lemma sorted_mono : forall l i j (Hsort : sorted l) (Hi : 0 <= i <= j)
                           (Hj : j < Zlength l),
    Znth i l <= Znth j l.
Proof.
induction l; intros.
* rewrite !Znth_nil. omega.
* 
 rewrite sorted_equiv in Hsort. destruct Hsort as [H9 Hsort].
 rewrite <- sorted_equiv in Hsort. rewrite Forall_forall in H9.
 rewrite Zlength_cons in Hj.
 destruct (zeq i 0).
 +
   subst i; rewrite Znth_0_cons. 
   destruct (zeq j 0).
   - subst j. rewrite Znth_0_cons. omega.
   - rewrite Znth_pos_cons by omega.
      apply H9.
      eapply Znth_In; [ | reflexivity]; omega.
 +
    rewrite !Znth_pos_cons by omega.
    apply IHl; auto; omega.
Qed.

Lemma In_sorted_range : forall lo hi x l (Hsort : sorted l) (Hlo : 0 <= lo <= hi)
                              (Hhi : hi <= Zlength l)
                              (Hin : In x (sublist lo hi l)),
    Znth lo l <= x <= Znth (hi - 1) l.
Proof.
  intros.
  generalize (In_Znth _ _ _ _ Hin); intros (i & Hrange & Hi).
  rewrite Zlength_sublist in Hrange by auto.
  rewrite Znth_sublist in Hi by omega.
  subst; split; apply sorted_mono; auto; omega.
Qed.

Lemma In_sorted_gt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l = n)
                            (Hgt : n < x),
    In x (sublist (i + 1) hi l).
Proof.
  intros.
  rewrite sublist_split with (mid := i + 1) in Hin; try omega.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range lo (i + 1) x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | omega]).
  replace (i + 1 - 1) with i in X by omega.
  specialize (X H); subst; omega.
Qed.

Lemma In_sorted_lt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l = n)
                            (Hgt : x < n),
    In x (sublist lo i l).
Proof.
  intros.
  rewrite sublist_split with (mid := i) in Hin; try omega.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range i hi x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | omega]).
  specialize (X H); subst; omega.
Qed.

Lemma Znth_In_sublist : forall A (d: Inhabitant A) i (l : list A) lo hi
  (Hlo : 0 <= lo <= i) (Hhi : i < hi <= Zlength l),
  In (Znth i l) (sublist lo hi l).
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
 destruct H0.
 assert (H6 := Int.min_signed_neg).
 forward_while (EX lo' : Z, EX hi' : Z,
    PROP  (0 <= lo' <= Int.max_signed; 
           Int.min_signed <= hi' <= Int.max_signed / 2;
           hi' <= Zlength contents;
           In tgt (sublist lo hi contents) <-> In tgt (sublist lo' hi' contents))
    LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
           temp _lo (Vint (Int.repr lo')); temp _hi (Vint (Int.repr hi')))
    SEP   (data_at sh (tarray tint (Zlength contents))
                   (map Vint (map Int.repr contents)) a)).
 * Exists lo; Exists hi; entailer!.
 * entailer!.
 *
  match goal with H : _ <-> _ |- _ => rename H into H_tgt_sublist end.
  forward.  (* mid =  (lo + hi) >> 1; *) {
   entailer!.
   clear - H8 HRE H7.
   set (j := Int.max_signed / 2) in *; compute in j; subst j.
   set (j := Int.max_signed) in *; compute in j; subst j.
   set (j := Int.min_signed) in *; compute in j; subst j.
   omega.
 }
  rewrite add_repr, Int.shr_div_two_p.
  change (two_p (Int.unsigned (Int.repr 1))) with 2. 
  assert (Hlo'hi':  lo' + hi' <= Int.max_signed). {
   transitivity (Int.max_signed / 2 + Int.max_signed / 2).
   - apply Zplus_le_compat; omega.
   - rewrite Zplus_diag_eq_mult_2, Z.mul_comm. apply Z_mult_div_ge; omega.
  }
  rewrite !Int.signed_repr by omega.
  set (mid := (lo' + hi') / 2) in *.
  assert (H13: 0 <= mid < Zlength contents)
    by (subst; split; [apply Z_div_pos | apply Zdiv_lt_upper_bound]; omega).
  assert (H15: lo' <= mid < hi')
    by (split; [apply Zdiv_le_lower_bound | apply Zdiv_lt_upper_bound]; omega).
  assert (H16: Int.min_signed <= Znth mid contents <= Int.max_signed)
    by (rewrite Forall_forall in H3; apply H3; eapply Znth_In; eauto).
  clear H3 Hlo'hi' H H0 H1.
  clearbody mid.
  forward. (* val = a[mid]; *)
  autorewrite with sublist.
  forward_if.
  - forward. (* return mid; *)
    Exists mid; entailer!.
    rewrite if_true; auto. 
    rewrite H_tgt_sublist.
    apply Znth_In_sublist; omega.
  - forward_if.
    + forward. (*  lo = mid + 1; *)
      Exists ((mid + 1), hi'); entailer!.
      rewrite H_tgt_sublist.
      split; intro Hin'.
      eapply In_sorted_gt; eauto; omega.
      eapply sublist_In_sublist; try apply Hin'; omega.
    + forward. (* hi=mid; *)
      Exists (lo', mid); entailer!.
      rewrite H_tgt_sublist.
      split; intro Hin'.
      eapply In_sorted_lt; eauto; omega.
      eapply sublist_In_sublist; try apply Hin'; omega.
 *
    forward.  (* return -1; *)
    Exists (-1); entailer!.
    rewrite if_false; auto.
    match goal with H : _ <-> _ |- _ => rewrite H end.
    rewrite sublist_nil1 by omega.
    clear; simpl; tauto.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward_call (gv _four,Ews,four_contents,3,0,4).
  { split. auto.
    change (Zlength four_contents) with 4.
    repeat constructor; computable.
  }
  Intro r; forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_search.
semax_func_cons body_main.
Qed.
