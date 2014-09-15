Require Import prod.
Require Import floyd.proofauto.
Require Import Clightdefs.

Definition bound_int (v : val) (b : Z) :=
  match v with
  | Vint i => -b < (Int.signed i) < b
  | _ => False
  end.
 
Definition product (a : Z -> val) (b : Z -> val) (i : Z) :=
  Val.mul (a i) (b i).
 
Definition product_spec :=
  DECLARE _product
  WITH b0 : val, sh : share, orig_a : Z -> val, orig_b : Z -> val, result : Z -> val, out0 : val, a0 : val
  PRE [_out OF (tptr tlong), _a OF (tptr tint), _b OF (tptr tint)]
    PROP (writable_share sh;
          forall i, 0 <= i < 10 -> is_long (orig_a i);
          forall i, 0 <= i < 10 -> is_long (orig_b i);
          forall i, 0 <= i < 10 -> bound_int (orig_a i) 134217728;
          forall i, 0 <= i < 10 -> bound_int (orig_b i) 134217728)
    LOCAL (`(eq out0) (eval_id _out);
           `(eq a0) (eval_id _a);
           `(eq b0) (eval_id _b);
           `isptr (eval_id _out);
           `isptr (eval_id _a);
           `isptr (eval_id _b))
    SEP (`(array_at tlong sh orig_a 0 10 a0);
         `(array_at tlong sh orig_b 0 10 b0);
         `(array_at_ tlong sh 0 1 out0))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (`(array_at tlong sh (product orig_a orig_b) 0 1 out0);
         `(array_at tlong sh orig_a 0 10 a0);
         `(array_at tlong sh orig_b 0 10 b0)).
 
Local Open Scope logic.
 
Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=  product_spec :: nil.
 
Lemma cast_l2i : forall (x : val), is_long x -> is_int (force_val (sem_cast_l2i I32 Signed x)).
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
Qed.
 
Lemma product_sumarray : semax_body Vprog Gprog f_product product_spec.
Proof.
start_function.
forward.
entailer!. omega.
assert(is_long (orig_a 0)).
apply H0 with (i:=0);
omega. 
apply cast_l2i.
exact H4.
forward.
entailer!. omega.
assert(is_long (orig_b 0)).
apply H1 with (i:=0).
omega.
apply cast_l2i.
exact H5.
forward.
eapply semax_pre.
instantiate (1 := 
(PROP  ()
      LOCAL 
      (`eq (eval_id _t3)
         (eval_expr
            (Ebinop Omul (Etempvar _t1 tint) (Etempvar _t2 tint) tint));
      `eq
        (`(eval_cast tlong tint)
           (`(repinject tlong)
              (`orig_b
                 (`force_signed_int
                    (eval_expr (Econst_int (Int.repr 0) tint))))))
        (eval_id _t2);
      `eq
        (`(eval_cast tlong tint)
           (`(repinject tlong)
              (`orig_a
                 (`force_signed_int
                    (eval_expr (Econst_int (Int.repr 0) tint))))))
        (eval_id _t1); `(eq out0) (eval_id _out); `(eq a0) (eval_id _a);
      `(eq b0) (eval_id _b); `isptr (eval_id _out); 
      `isptr (eval_id _a); `isptr (eval_id _b))
      SEP  (`(array_at tlong sh orig_a 0 10 a0);
      `(array_at tlong sh orig_b 0 10 b0); `(array_at_ tlong sh 0 1 _out)))).
entailer!.
forward.