Require Import floyd.proofauto.
Require Import progs.field_loadstore.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Lemma Znth_map: forall {A B} n xs d (f: A -> B),
  Znth n (map f xs) (f d) = f (Znth n xs d).
Proof.
  intros.
  unfold Znth.
  if_tac.
  + reflexivity.
  + apply map_nth.
Qed.

Lemma legal_Znth_map: forall {A B} n xs dA dB (f: A -> B),
  0 <= n < Zlength xs ->
  Znth n (map f xs) dB = f (Znth n xs dA).
Proof.
  intros.
  unfold Znth.
  if_tac.
  + omega.
  + apply nth_map'.
    rewrite Zlength_correct in H.
    destruct H.
    apply Z2Nat.inj_lt in H1; [ | omega | omega].
    rewrite Nat2Z.id in H1.
    exact H1.
Qed.

Definition t_struct_b := Tstruct _b noattr.

Definition sub_spec (sub_id: ident) :=
 DECLARE sub_id
  WITH v : val * list (val*val) , p: val
  PRE  []
        PROP  (is_int I8 Signed (snd (nth 1%nat (snd v) (Vundef, Vundef))))
        LOCAL (gvar _p p)
        SEP   (data_at Ews t_struct_b v p)
  POST [ tint ]
        PROP() LOCAL()
        SEP(data_at Ews t_struct_b (snd (nth 1%nat (snd v) (Vundef, Vundef)), snd v) p).

Definition sub_spec' (sub_id: ident) :=
 DECLARE sub_id
  WITH v : reptype t_struct_b, p: val
  PRE  []
        PROP  (is_int I8 Signed (proj_reptype _ (DOT _y2 SUB 1 DOT _x2) v))
        LOCAL (gvar _p p)
        SEP   (data_at Ews t_struct_b v p)
  POST [ tint ]
        PROP() LOCAL()
        SEP(data_at Ews t_struct_b
           (upd_reptype t_struct_b (DOT _y1) v
             (proj_reptype t_struct_b (StructField _x2 :: ArraySubsc 1 :: StructField _y2 :: nil) v))
           p).

Lemma spec_coincide: sub_spec' = sub_spec.
Proof.
(*reflexivity.*)
Abort.

Definition Gprog : funspecs :=   ltac:(with_library prog [
    sub_spec _sub1; sub_spec _sub2; sub_spec _sub3]).

Lemma body_sub1:  semax_body Vprog Gprog f_sub1 (sub_spec _sub1).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
Qed.

Lemma body_sub2:  semax_body Vprog Gprog f_sub2 (sub_spec _sub2).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
Qed.

Lemma body_sub3:  semax_body Vprog Gprog f_sub3 (sub_spec _sub3).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
  forward.
Qed.

