Require Import VST.progs.prod.
Require Import VST.floyd.proofauto.

Definition bound_int (v : val) (b : Z) :=
  match v with
  | Vint i => -b < (Int.signed i) < b
  | _ => False
  end.

Definition product a b := map (fun vp => Val.mul (fst vp) (snd vp)) (combine a b).

Definition product_spec :=
  DECLARE _product
  WITH b0 : val, sh : share, orig_a : list val, orig_b : list val, out0 : val, a0 : val
  PRE [_out OF (tptr tlong), _a OF (tptr tint), _b OF (tptr tint)]
    PROP (writable_share sh;
          length orig_a = 10%nat;
          length orig_b = 10%nat;
          forall i, 0 <= i < 10 -> is_long (Znth i orig_a Vundef);
          forall i, 0 <= i < 10 -> is_long (Znth i orig_b Vundef);
          forall i, 0 <= i < 10 -> bound_int (Znth i orig_a Vundef) 134217728;
          forall i, 0 <= i < 10 -> bound_int (Znth i orig_b Vundef) 134217728)
    LOCAL (temp _out out0;
           temp _a a0;
           temp _b b0;
           `isptr (eval_id _out);
           `isptr (eval_id _a);
           `isptr (eval_id _b))
    SEP (`(data_at sh (tarray tlong 10) orig_a a0);
         `(data_at sh (tarray tlong 10) orig_b b0);
         `(data_at_ sh (tarray tlong 10) out0))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (`(data_at sh (tarray tlong 10) orig_a a0);
         `(data_at sh (tarray tlong 10) orig_b b0);
         `(data_at sh (tarray tlong 10) (product orig_a orig_b) out0)).

Local Open Scope logic.

Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=   ltac:(with_library prog [product_spec]).

Lemma cast_l2i : forall (x : val), is_long x -> is_int I32 Signed (force_val (sem_cast_l2i I32 Signed x)).
Proof.
intros.
unfold force_val, sem_cast_l2i.
induction x.
auto.
auto.
Focus 2.
auto.
Focus 2.
auto.
auto.
inversion H.
Qed.

Lemma product_sumarray : semax_body Vprog Gprog f_product product_spec.
Proof.
start_function.
forward.
  entailer!.
  apply cast_l2i.
  apply H2.
  omega.
forward.
  entailer!.
  apply cast_l2i.
  apply H3.
  omega.
forward.
forward.
forward.
Abort.