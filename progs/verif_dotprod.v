Require Import VST.floyd.proofauto.
Require Import VST.progs.dotprod.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Local Open Scope logic.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.

Definition add_spec :=
 DECLARE _add
  WITH x: val, y : val, z: val, fy : list float, fz: list float
  PRE  [ tptr tdouble, tptr tdouble, tptr tdouble]
      PROP ()
      PARAMS (x; y; z)
      SEP (data_at_ Tsh (tarray tdouble 3)  x ;
             data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
             data_at Tsh (tarray tdouble 3) (map Vfloat fz) z)
  POST [ tvoid ]
      PROP ()
      RETURN ()
      SEP (data_at Tsh (tarray tdouble 3) (map Vfloat (map2 Float.add fy fz)) x;
             data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
             data_at Tsh (tarray tdouble 3) (map Vfloat fz) z).

Definition dotprod (fx fy : list float) : float :=
  fold_left Float.add (map2 Float.mul fx fy) Float.zero .

Definition dotprod_spec :=
 DECLARE _dotprod
  WITH n: Z, x: val, y : val, fx : list float, fy: list float, sh: share
  PRE  [ tint, tptr tdouble, tptr tdouble]
      PROP (0 <= n < Int.max_signed)
      PARAMS (Vint (Int.repr n); x; y)
      SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
             data_at Tsh (tarray tdouble n) (map Vfloat fy) y)
  POST [ tdouble ]
      PROP ()
      RETURN (Vfloat (dotprod fx fy))
      SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
             data_at Tsh (tarray tdouble n) (map Vfloat fy) y).


Definition Gprog : funspecs :=   ltac:(with_library prog [add_spec; dotprod_spec]).

Lemma map2_app:
 forall (A B C: Type) (f: A -> B -> C) al al' bl bl',
  Zlength al = Zlength bl ->
  Zlength al' = Zlength bl' ->
   map2 f (al ++ al') (bl ++ bl') = map2 f al bl ++ map2 f al' bl'.
Proof.
intros.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H. apply Nat2Z.inj in H0.
revert bl H al' bl' H0; induction al; intros.
*
destruct bl; inv H.
simpl. auto.
*
destruct bl.
inv H.
simpl.
f_equal.
auto.
Qed.

Lemma Zlength_map2: forall A B C (f: A -> B -> C) fy fz,
  Zlength fy = Zlength fz -> Zlength (map2 f fy fz) = Zlength fy.
Proof.
intros.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H. f_equal.
revert fz H; induction fy; destruct fz; intros; inv H.
auto.
simpl. f_equal; auto.
Qed.

Lemma Znth_map2:
 forall A B C (a: Inhabitant A) (b: Inhabitant B) (c: Inhabitant C) (f: A -> B -> C) (al: list A) (bl: list B) i,
  Zlength al = Zlength bl ->
  0 <= i < Zlength al ->
  Znth i (map2 f al bl) = f (Znth i al) (Znth i bl).
Proof.
intros.
rewrite !Zlength_correct in *.
apply Nat2Z.inj in H. f_equal.
unfold Znth.
if_tac. lia.
assert (Z.to_nat i < length al)%nat.
rewrite <- (Nat2Z.id (length al)).
apply Z2Nat.inj_lt; try lia.
clear H0 H1.
forget (Z.to_nat i) as j. clear i.
revert al bl H H2; induction j; intros.
destruct al; inv H2.
destruct bl; inv H.
simpl. auto.
destruct bl; inv H.
simpl. auto.
destruct al; simpl in H2; try lia.
destruct bl; inv H.
simpl.
apply IHj; auto.
lia.
Qed.

Lemma body_dotprod:  semax_body Vprog Gprog f_dotprod dotprod_spec.
Proof.
start_function.
forward. (* sum = 0.0; *)
forward_for_simple_bound n
   (EX i:Z,
      PROP ()
      LOCAL (temp _sum (Vfloat (dotprod (sublist 0 i fx) (sublist 0 i fy))); temp _x x; temp _y y; temp _n (Vint (Int.repr n)))
      SEP (data_at Tsh (tarray tdouble n) (map Vfloat fx) x;
             data_at Tsh (tarray tdouble n) (map Vfloat fy) y)).
* (* initializer *)
entailer!.
* (* body *)
assert_PROP (Zlength fx = n /\ Zlength fy = n). {
    entailer!. autorewrite with sublist in *; split; auto.
} destruct H1.
forward.
forward. 
rewrite !Znth_map by lia.
forward. 
  entailer!.
  autorewrite with sublist in *.
  f_equal.
  rewrite (sublist_split 0 i _ fx) by lia.
  rewrite (sublist_split 0 i _ fy) by lia.
  unfold dotprod.
 rewrite map2_app by list_solve.
 rewrite fold_left_app.
 rewrite !sublist_len_1 by list_solve.
 simpl. auto.
*
 forward.
 autorewrite with sublist in *.
 autorewrite with sublist.
 entailer!.
Qed.

Lemma body_add:  semax_body Vprog Gprog f_add add_spec.
Proof.
start_function.
Hint Rewrite Zlength_map2 using (try Zlength_solve; fail 4) : Zlength.
pose (fx := map2 Float.add fy fz).
assert_PROP (Zlength fx = 3 /\ Zlength fy = 3 /\ Zlength fz = 3). {
  entailer!. subst fx. list_solve.
} destruct H as [Hx [Hy Hz]].
forward_for_simple_bound 3
   (EX i:Z,
      PROP ()
      LOCAL (temp _x x; temp _y y; temp _z z)
      SEP (data_at Tsh (tarray tdouble 3) 
          (map Vfloat (sublist 0 i fx) ++ repeat Vundef (Z.to_nat (3-i))) x;
   data_at Tsh (tarray tdouble 3) (map Vfloat fy) y;
   data_at Tsh (tarray tdouble 3) (map Vfloat fz) z)).
* (* initializer *)
entailer!. simpl; entailer!.
* (* body *)
forward. (* x[i] = y[i] + z[i]; *)
forward.
forward.
entailer!. {
  simpl force_val.
  Hint Rewrite (Znth_map2 _ _ _ Inhabitant_float Inhabitant_float Inhabitant_float) using Zlength_solve : Znth.
  Hint Rewrite (@Znth_map _ Inhabitant_float) using Zlength_solve : Znth.
  subst fx. list_solve.
}
*
 forward.
 autorewrite with sublist. subst fx. auto.
Qed.

Definition Svector_add (n: Z) (_i _x _y _z : ident) :=
   Ssequence (Sset _i (Econst_int (Int.repr 0) tint))
     (Sloop
        (Ssequence
           (Sifthenelse
              (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr n) tint) tint)
              Sskip
              Sbreak)
           (Sassign
              (Ederef
                 (Ebinop Oadd (Etempvar _x (tptr tdouble)) (Etempvar _i tint)
                    (tptr tdouble)) tdouble)
              (Ebinop Oadd
                 (Ederef
                    (Ebinop Oadd (Etempvar _y (tptr tdouble))
                       (Etempvar _i tint) (tptr tdouble)) tdouble)
                 (Ederef
                    (Ebinop Oadd (Etempvar _z (tptr tdouble))
                       (Etempvar _i tint) (tptr tdouble)) tdouble) tdouble)))
        (Sset _i
           (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))).

Definition vector_add (fx fy: Z -> float) i :=
    Float.add (fx i) (fy i).



