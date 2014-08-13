Require Import floyd.proofauto.
Require Import progs.dotprod.

Local Open Scope logic.

Definition add_spec :=
 DECLARE _add
  WITH n: Z, x: val, y : val, z: val, fy : Z -> float, fz: Z -> float
  PRE  [_n OF tint, _x OF tptr tdouble, _y OF tptr tdouble, _z OF tptr tdouble] 
      PROP (0 <= n <= Int.max_signed)
      LOCAL (`(eq (Vint (Int.repr n))) (eval_id _n);
                  `(eq x) (eval_id _x);
                  `(eq y) (eval_id _y);
                  `(eq z) (eval_id _z))
      SEP (`(array_at_ tdouble Tsh 0 n x) ;
             `(array_at tdouble Tsh (Vfloat oo fy) 0 n y);
             `(array_at tdouble Tsh (Vfloat oo fz) 0 n z))
  POST [ tvoid ] 
      PROP ()
      LOCAL ()
      SEP (`(array_at tdouble Tsh (Vfloat oo (fun i => Float.add (fy i) (fz i))) 0 n x);
             `(array_at tdouble Tsh (Vfloat oo fy) 0 n y);
             `(array_at tdouble Tsh (Vfloat oo fz) 0 n z) ).

Definition dotprod (n: Z) (fx fy : Z -> float) : float :=
  fold_range (fun i sum => Float.add sum (Float.mul (fx i) (fy i)))
            Float.zero 0 n.

Definition dotprod_spec :=
 DECLARE _dotprod
  WITH n: Z, x: val, y : val, fx : Z -> float, fy: Z -> float, sh: share
  PRE  [_n OF tint, _x OF tptr tdouble, _y OF tptr tdouble] 
      PROP (0 <= n <= Int.max_signed)
      LOCAL (`(eq (Vint (Int.repr n))) (eval_id _n);
                  `(eq x) (eval_id _x);
                  `(eq y) (eval_id _y))
      SEP (`(array_at tdouble sh (Vfloat oo fx) 0 n x);
             `(array_at tdouble sh (Vfloat oo fy) 0 n y))
  POST [ tdouble ] 
      PROP ()
      LOCAL (`(eq (Vfloat (dotprod n fx fy))) retval)
      SEP (`(array_at tdouble sh (Vfloat oo fx) 0 n x);
             `(array_at tdouble sh (Vfloat oo fy) 0 n y) ).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := 
     add_spec::dotprod_spec::nil.

Lemma dotprod_one_more:
  forall i f g, dotprod (i+1) f g = Float.add (dotprod i f g) (Float.mul (f i) (g i)).
Admitted.

Lemma body_dotprod:  semax_body Vprog Gprog f_dotprod dotprod_spec.
Proof.
start_function.
name n_ _n.
name i_ _i.
name x_ _x.
name y_ _y.

forward. (* sum = 0.0; *)
forward_for_simple_bound n
   (EX i:Z,
      PROP ()
      LOCAL (`(eq (Vfloat (dotprod i fx fy))) (eval_id _sum);
                  `(eq x) (eval_id _x);
                  `(eq y) (eval_id _y))
      SEP (`(array_at tdouble sh (Vfloat oo fx) 0 n x);
             `(array_at tdouble sh (Vfloat oo fy) 0 n y))).
* (* initializer *)
entailer!.
* (* body *)
forward_nl;
entailer!.
rewrite <- H1; f_equal.
apply dotprod_one_more.
* (*after the for-loop *)
 forward. (*   return; *)
Qed.

Lemma body_add:  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
name i_ _i.
name x_ _x.
name y_ _y.
name z_ _z.

forward_for_simple_bound n
   (EX i:Z,
      PROP ()
      LOCAL (`(eq x) (eval_id _x);
                  `(eq y) (eval_id _y);
                  `(eq z) (eval_id _z))
      SEP (`(array_at tdouble Tsh
                   (fun j => if zlt j i then Vfloat (Float.add (fy j) (fz j)) else Vundef)
                  0 n x) ;
             `(array_at tdouble Tsh (Vfloat oo fy) 0 n y);
             `(array_at tdouble Tsh (Vfloat oo fz) 0 n z))).
* (* initializer *)
entailer!.
unfold array_at_.
apply array_at_ext'; intros. if_tac; auto. omega.
* (* body *)
forward_nl. (* x[i] = y[i] + z[i]; *)
entailer!.
apply array_at_ext'; intros.
unfold upd. if_tac. subst i0. rewrite if_true by omega. auto.
if_tac. rewrite if_true by omega; auto. rewrite if_false by omega; auto.
* (*after the for-loop *)
 forward. (*   return; *)
 cancel.
 apply array_at_ext'; intros. rewrite if_true by omega. reflexivity.
Qed.

