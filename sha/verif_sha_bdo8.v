Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.

Definition load8 id ofs :=
 (Sset id
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr ofs) tint) (tptr tuint)) tuint)).

Lemma Znth_is_int:
 forall i r,
  0 <=  i < Zlength r ->
  is_int I32 Unsigned (Znth i (map Vint r) Vundef).
Proof.
intros.
unfold Znth.
rewrite if_false by omega.
rewrite (nth_map' Vint Vundef Int.zero).
apply I.
destruct H as [H0 H]; rewrite Zlength_correct in H.
rewrite <- (Z2Nat.id i) in H; auto.
apply Nat2Z.inj_lt in H; auto.
Qed.

Lemma sha256_block_load8:
  forall (Espec : OracleKind)
     (data: val) (r_h: list int) (ctx: val) kv
   (H5 : length r_h = 8%nat),
     semax
      (initialized _data
         (func_tycontext f_sha256_block_data_order Vprog Gtot))
  (PROP  ()
   LOCAL  (temp _data data; temp _ctx ctx; temp _in data;
                gvar  _K256 kv)
   SEP  (field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint r_h) ctx))
   (Ssequence (load8 _a 0)
     (Ssequence (load8 _b 1)
     (Ssequence (load8 _c 2)
     (Ssequence (load8 _d 3)
     (Ssequence (load8 _e 4)
     (Ssequence (load8 _f 5)
     (Ssequence (load8 _g 6)
     (Ssequence (load8 _h 7)
         Sskip))))))))
  (normal_ret_assert
  (PROP  ()
   LOCAL  (temp _a (Vint (nthi r_h 0));
                temp _b (Vint (nthi r_h 1));
                temp _c (Vint (nthi r_h 2));
                temp _d (Vint (nthi r_h 3));
                temp _e (Vint (nthi r_h 4));
                temp _f (Vint (nthi r_h 5));
                temp _g (Vint (nthi r_h 6));
                temp _h (Vint (nthi r_h 7));
                temp _data data; temp _ctx ctx; temp _in data;
                gvar  _K256 kv)
   SEP  (field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint r_h) ctx))).
Proof.
intros.
unfold load8.
abbreviate_semax.
assert (H5': Zlength r_h = 8%Z)
  by (rewrite Zlength_correct; rewrite H5; reflexivity).
do 8 forward.
entailer!.
Qed.

Definition get_h (n: Z) :=
    Sset _t
        (Ederef
           (Ebinop Oadd
              (Efield
                 (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr n) tint) (tptr tuint)) tuint).

Definition add_h (n: Z) (i: ident) :=
   Sassign
       (Ederef
          (Ebinop Oadd
             (Efield
                (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                   t_struct_SHA256state_st) _h (tarray tuint 8))
             (Econst_int (Int.repr n) tint) (tptr tuint)) tuint)
       (Ebinop Oadd (Etempvar _t tuint) (Etempvar i tuint) tuint).

Definition add_them_back :=
 [get_h 0; add_h 0 _a;
  get_h 1; add_h 1 _b;
  get_h 2; add_h 2 _c;
  get_h 3; add_h 3 _d;
  get_h 4; add_h 4 _e;
  get_h 5; add_h 5 _f;
  get_h 6; add_h 6 _g;
  get_h 7; add_h 7 _h].

Fixpoint add_upto (k: nat) (u v: list int) {struct k} :=
 match k with
 | O => u
 | S k' => match u,v with
                | u1::us, v1::vs => Int.add u1 v1 :: add_upto k' us vs
                | _, _ => u
                end
 end.

Lemma length_add_upto:
  forall i r s,
   length r = length s  ->
   length (add_upto i r s) = length r.
Proof.
induction i; destruct r,s; intros;
 inv H; simpl; auto.
Qed.


Lemma force_lengthn_short:
  forall {A} i (b: list A) v,
     (i <= length b)%nat -> force_lengthn i b v = firstn i b.
Proof.
induction i; destruct b; intros.
reflexivity.
reflexivity.
inv H.
simpl. f_equal. apply IHi. simpl in H. omega.
Qed.

Lemma add_upto_S:
  forall (atoh regs : list int) (i : nat),
  length atoh = 8%nat ->
  length regs = 8%nat ->
   (i < 8)%nat ->
  map Vint (add_upto (S i) regs atoh) =
  upd_Znth (Z.of_nat i) (map Vint (add_upto i regs atoh))
   (Vint
     (Int.add (nthi (add_upto i regs atoh) (Z.of_nat i))
        (nthi atoh (Z.of_nat i)))).
Proof.
intros. rename H1 into H4.
 assert ( i < length (add_upto i regs atoh))%nat
    by (rewrite length_add_upto; omega).
 unfold upd_Znth.
 rewrite !sublist_map, <- map_cons, <- map_app.
 f_equal.

assert (H18: length regs = length atoh) by congruence.
assert (H19: (i < length regs)%nat) by omega.
clear - H18 H19.
revert regs atoh H18 H19; induction i; destruct regs,atoh; intros;
try solve [inv H19]; inv H18.
simpl.
f_equal.
change (i::regs) with ([i]++regs).
autorewrite with sublist. auto.
simpl in H19.
change (add_upto (S (S i)) (i0 :: regs) (i1 :: atoh))
  with (Int.add i0 i1 :: add_upto (S i) regs atoh).
simpl in H19.
rewrite (IHi regs atoh); auto; [ | omega].
clear IHi.
simpl add_upto.
rewrite (sublist_split 0 1 (Z.of_nat (S i))); try omega.
change (@sublist int 0 1) with (@sublist int 0 (0+1)).
rewrite sublist_singleton with (d:=Int.zero); try omega.
rewrite inj_S.
simpl.
autorewrite with sublist.
f_equal.
f_equal.
change (cons (Int.add i0 i1)) with (app [Int.add i0 i1]).
rewrite sublist_app2 by (autorewrite with sublist; omega).
f_equal.
autorewrite with sublist; omega.
f_equal.
f_equal.
unfold nthi.
rewrite Z2Nat.inj_succ by omega.
reflexivity.
unfold nthi.
rewrite Z2Nat.inj_succ by omega.
reflexivity.
change (cons (Int.add i0 i1)) with (app [Int.add i0 i1]).
rewrite sublist_app2 by (autorewrite with sublist; omega).
f_equal.
autorewrite with sublist; omega.
autorewrite with sublist; omega.
autorewrite with sublist. Omega1.
rewrite inj_S.
split; try omega.
rewrite Zlength_cons.
unfold Z.succ.
apply Zplus_le_compat_r.
rewrite Zlength_correct.
rewrite length_add_upto; auto.
apply Nat2Z.inj_le; auto.
omega.
Qed.

Lemma upd_reptype_array_gso: (* perhaps move to floyd? *)
 forall t a v i j,
    0 <= j <= Zlength a ->
    0 <= i < Zlength a ->
    i<>j ->
    Znth i (upd_Znth j a v) (default_val t) = Znth i a (default_val t).
Proof.
intros.
unfold upd_Znth.
assert (i<j \/ i>j) by omega.
clear H1; destruct H2.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
change (cons v) with (app [v]).
autorewrite with sublist; auto.
f_equal; omega.
Qed.

Lemma int_add_upto:
  forall (regs atoh: list int),
   Datatypes.length regs = 8%nat ->
   Datatypes.length atoh = 8%nat ->
   forall (j:nat)  (i:Z),
     j = Z.to_nat i ->
     0 <= i < 8 ->
     is_int I32 Unsigned (Znth i (map Vint (add_upto j  regs atoh)) Vundef).
Proof.
intros until 2.
  assert (ZR: Zlength regs = 8) by ( rewrite Zlength_correct, H; reflexivity).
  induction j; intros.
  simpl. apply Znth_is_int; omega.
  unfold Znth.
  rewrite if_false by omega.
 rewrite nth_map' with (d' := Int.zero).
  apply I.
  rewrite length_add_upto by omega.
  rewrite H. apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by omega. apply H2.
Qed.

Lemma add_s:
  forall (regs atoh: list int),
   Datatypes.length regs = 8%nat ->
   Datatypes.length atoh = 8%nat ->
 forall i i',
    (i < 8)%nat ->
    i' = Z.of_nat i ->
   upd_Znth i' (map Vint (add_upto i regs atoh))
       (force_val
              (sem_cast_neutral
                 (force_val
                    (sem_add_default tuint tuint
                       (Znth i' (map Vint (add_upto i regs atoh)) Vundef)
                       (Vint (nthi atoh i')))))) =
     map Vint (add_upto (S i) regs atoh).
Proof.
intros.
assert (is_int I32 Unsigned (Znth i' (map Vint (add_upto i regs atoh)) Vundef)).
 apply  Znth_is_int.   rewrite Zlength_correct, length_add_upto, H.
 change (Z.of_nat 8) with 8; omega. rewrite H,H0;  auto.
subst i'.
rewrite add_upto_S; try omega.
f_equal.
destruct (Znth (Z.of_nat i) (map Vint (add_upto i regs atoh)) Vundef) eqn:?;
   try contradiction H3.
simpl.
f_equal. f_equal.
unfold Znth in Heqv.
rewrite if_false in Heqv.
unfold nthi.
rewrite Nat2Z.id in Heqv|-*.
rewrite nth_map' with (d':=Int.zero) in Heqv.
inv Heqv. auto.
rewrite length_add_upto; try congruence.
clear; omega.
Qed.

Lemma add_upto_8:
  forall (regs atoh: list int),
   Datatypes.length regs = 8%nat ->
   Datatypes.length atoh = 8%nat ->
    add_upto 8 regs atoh = map2 Int.add regs atoh.
Proof.
intros.
destruct atoh as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; inv H0.
destruct regs as [ | a' [ | b' [ | c' [ | d' [ | e' [ | f' [ | g' [ | h' [ | ]]]]]]]]]; inv H.
simpl; auto.
Qed.

Lemma add_them_back_proof:
  forall (Espec : OracleKind)
     (regs regs': list int) (ctx: val) kv,
     length regs = 8%nat ->
     length regs' = 8%nat ->
     semax  (initialized _i Delta_loop1)
   (PROP  ()
   LOCAL  (temp _ctx ctx;
                temp _a  (Vint (nthi regs' 0));
                temp _b  (Vint (nthi regs' 1));
                temp _c  (Vint (nthi regs' 2));
                temp _d  (Vint (nthi regs' 3));
                temp _e  (Vint (nthi regs' 4));
                temp _f  (Vint (nthi regs' 5));
                temp _g  (Vint (nthi regs' 6));
                temp _h  (Vint (nthi regs' 7));
                gvar  _K256 kv)
   SEP
   (field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint regs) ctx))
   (sequence add_them_back Sskip)
  (normal_ret_assert
   (PROP() LOCAL(temp _ctx ctx; gvar _K256 kv)
    SEP (field_at Tsh t_struct_SHA256state_st  [StructField _h]
                (map Vint (map2 Int.add regs regs')) ctx))).
Proof.
intros.
rename regs' into atoh.
unfold sequence, add_them_back.
change regs with  (add_upto 0 regs atoh) at 1.
unfold get_h, add_h.
abbreviate_semax.
assert (ZR: Zlength regs = 8) by (rewrite Zlength_correct, H; reflexivity).
assert (INT_ADD_UPTO := int_add_upto _ _ H H0).
assert (ADD_S := add_s _ _ H H0).

Opaque add_upto.

(* TODO remove this line and update proof (should become simpler) *)
Ltac canon_load_result Hresult ::= idtac.

forward.
entailer!. apply INT_ADD_UPTO; auto; computable.
forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
forward; forward.
simpl upd_Znth; rewrite ADD_S by (try reflexivity; clear; omega).
rewrite (add_upto_8 _ _ H H0).
entailer!.
Qed.



