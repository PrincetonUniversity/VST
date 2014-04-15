Require Import MirrorShard.Expr.
Import Compare_dec.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import ExtLib.Tactics.
Require Import Equalities.
Require Import compcert.lib.Maps.
Require Import compcert.lib.UnionFind.




Fixpoint tvar_comp t1 t2 : Datatypes.comparison :=
match t1, t2 with
| tvProp, tvProp => Eq
| tvType n1, tvType n2 => nat_compare n1 n2
| tvProp, _ => Lt
| _, _ => Gt
end.

Fixpoint expr_comp a b: Datatypes.comparison :=
match a, b with  
| Var x, Var y => nat_compare x y
| Func f1 l1, Func f2 l2 => 
     let fcomp := nat_compare f1 f2 in
     match fcomp with 
       | Datatypes.Eq => 
         (fix expr_comp' l1 l2 : Datatypes.comparison :=
            match l1, l2 with
              | nil, nil => Datatypes.Eq
              | h::t, nil => Datatypes.Gt
              | nil, h::t => Datatypes.Lt
              | h1::t1, h2::t2 =>
                let r := (expr_comp h1 h2) in
                match r  with
                  | Datatypes.Eq => expr_comp' t1 t2
                  | _ => r
                end
            end) l1 l2
       | _ => fcomp
     end
| Equal t1 e1 e2, Equal t2 e3 e4 =>
  let r := tvar_comp t1 t2 in
  match r with
  | Datatypes.Eq => 
    let c := expr_comp e1 e3 in
    match c with
      | Datatypes.Eq => expr_comp e2 e4
      | _ => c
    end 
  | _ => r
  end
| UVar x, UVar y => nat_compare x y
| Not e1, Not e2 => expr_comp e1 e2
| Var _, _ => Datatypes.Lt
| _, Var _ => Datatypes.Gt
| Func _ _, _ => Datatypes.Lt
| _, Func _ _ => Datatypes.Gt
| Equal _ _ _, _ => Datatypes.Lt
| _, Equal _  _ _ => Datatypes.Gt
| Not _, _ => Datatypes.Lt
| _, Not _ => Datatypes.Gt
end.

Definition eq_expr a b : bool :=
match expr_comp a b with
| Datatypes.Eq => true
| _ => false
end.

Definition lt_prop_expr a b :=
match expr_comp a b with
| Datatypes.Lt => True
| _ => False
end.

Lemma nat_compare_refl : forall a, nat_compare a a = Datatypes.Eq.
Proof.
induction a. auto.
simpl. apply IHa.
Qed.

Lemma nat_compare_sym : forall a b, nat_compare a b = Datatypes.Eq -> 
                                     nat_compare b a = Datatypes.Eq.
Proof.
induction a; intros; auto.
simpl. destruct b; simpl in *; congruence.
destruct b; simpl in *; try congruence; apply IHa; auto. 
Qed.

Lemma eq_expr_refl : forall x : expr, eq_expr x x= true.
intros;
induction x; auto.
  + unfold eq_expr. simpl.
    rewrite nat_compare_refl. auto.
  + unfold eq_expr. simpl.
    rewrite nat_compare_refl. auto.
  + unfold eq_expr. simpl.
    rewrite nat_compare_refl. 
      induction l; auto.
        -  inv H. unfold eq_expr in H2. destruct (expr_comp a a); inv H2.
           apply IHl.
           auto.
  + unfold eq_expr in *. simpl. destruct t. simpl.
    destruct (expr_comp x1 x1); inv IHx1.
    auto.
    simpl. rewrite nat_compare_refl.
    destruct (expr_comp x1 x1); inv IHx1.
    auto.
Qed.

Lemma expr_comp_refl : forall x, expr_comp x x = Eq.
Proof.
intros.
assert (X := eq_expr_refl x). unfold eq_expr in *.
consider (expr_comp x x). auto.
Qed.

Lemma expr_comp_eq_iff : forall a b, expr_comp a b = Eq <-> a = b.
Proof.
intros.
split; intros. generalize dependent b.
 + induction a; intros; simpl in *; auto.
     - destruct b; inv H.
       rewrite nat_compare_eq_iff in H1. auto.
     - consider b; intros; try congruence.
       rewrite nat_compare_eq_iff in H0. auto.
     - destruct b; inv H0.
       pose (expr_comp' := 
               (fix expr_comp' (l1 l0 : list expr) {struct l1} :
                 Datatypes.comparison :=
                 match l1 with
                 | nil => match l0 with
                          | nil => Eq
                          | _ :: _ => Lt
                          end
                 | h1 :: t1 =>
                     match l0 with
                     | nil => Gt
                     | h2 :: t2 =>
                         match expr_comp h1 h2 with
                         | Eq => expr_comp' t1 t2
                         | Lt => expr_comp h1 h2
                         | Gt => expr_comp h1 h2
                         end
                     end
                 end)).
       fold expr_comp' in H2.
       consider (nat_compare f f0); intros; try congruence.
       rewrite nat_compare_eq_iff in H0. subst. f_equal.
       generalize dependent l0.
       induction l; intros. 
         * consider l0; intros; simpl in *; auto; congruence.
         * simpl in *. inv H. 
           consider (l0); intros; try congruence.
           consider (expr_comp a e); intros; try congruence.
           rewrite (H3 e) by auto.
           erewrite IHl by eauto. auto.
     - consider b; try congruence; intros.
       consider (expr_comp a1 e); try congruence; intros.
        assert (t = t0). destruct t, t0; inv H1; auto.
        consider (nat_compare n n0); intros; try congruence.
        rewrite nat_compare_eq_iff in *; auto. subst. 
        erewrite IHa1 by eauto. f_equal.
        consider (tvar_comp t0 t0); intros; try congruence.
        eauto.
        consider (tvar_comp t t0); try congruence.
        consider (tvar_comp t t0); try congruence.   
     - destruct b; inv H.
       erewrite IHa; eauto.
 + subst. assert (x:= eq_expr_refl b). unfold eq_expr in x.
   destruct (expr_comp b b); inv x; auto.
Qed.

Lemma expr_eqb_eq : forall x y : expr, eq_expr x y = true <-> x = y.
  Proof.
    unfold eqb, eq_expr; intuition;
    consider (expr_comp x y); intros;
    try apply expr_comp_eq_iff in H; auto;
    subst; try apply expr_comp_refl in H0; congruence.
    Qed.
      

Lemma expr_eq_dec : forall (x y: expr), {x=y} + {x<>y}.
Proof.
intros.
case_eq (eq_expr x y); intros.
apply (expr_eqb_eq x y) in H. subst; auto.
right. intuition. subst. rewrite eq_expr_refl in H. congruence.
Defined.

Module Type BOOL_EQUALITY_TYPE.
  Variable t: Type.
  Variable beq : t -> t -> bool.
  Parameter beq_true : forall x y, beq x y = true <-> x = y.
End BOOL_EQUALITY_TYPE.

Module EXPR_EQUALITY <: BOOL_EQUALITY_TYPE.
  Definition t := expr.
  Definition beq := eq_expr.
  Definition beq_true :=expr_eqb_eq.
End EXPR_EQUALITY.


Module EMAP_BOOL (X : BOOL_EQUALITY_TYPE) <: UnionFind.MAP.
  Definition elt := X.t.
  Definition elt_eq : forall (x y : elt), {x = y} + {x <> y}.
    unfold elt. intros.
    case_eq (X.beq x y); intros.
    apply X.beq_true in H. auto.
    right.
    intro. apply X.beq_true in H0. congruence.
  Defined.
  Definition t (A : Type) : Type :=  (elt -> option A).
  Definition empty (A : Type) : t A := fun _ => None. 
  Definition get {A : Type} (e : elt) (m : t A) : option A := m e. 
  Definition set  {A: Type} (e: elt) (v : A) (m :t A) : t A :=
                         fun ne => if X.beq ne e then Some v else m ne.
  Lemma gempty: forall (A: Type) (x: elt), get x (empty A) = None.
  Proof.
    intros. unfold empty. unfold get. auto.
  Qed.

  Lemma gsspec: forall (A: Type) (x y: elt) (v: A) (m: t A),
    get x (set y v m) = if elt_eq x y then Some v else get x m.
    Proof.
      intros. unfold get, set.
      case_eq (X.beq x y); intros. rewrite X.beq_true in H.
      subst. destruct (elt_eq y y); intuition.
      destruct (elt_eq x y); intuition. rewrite <- X.beq_true in e.
      congruence.
    Qed.
      
End EMAP_BOOL.

Module EXPR_MAP := EMAP_BOOL EXPR_EQUALITY.

Module EXPR_UF := UF EXPR_MAP.

Definition beq_tvar x y :=
match x, y with
| tvProp, tvProp => true
| tvType n1 , tvType n2 => beq_nat n1 n2
| _, _ => false
end.

Lemma beq_tvar_true_iff x y:
beq_tvar x y = true <-> x = y.
Proof.
intuition;
destruct x,y; simpl in *; try congruence.
apply beq_nat_true in H. subst; auto.
rewrite beq_nat_true_iff. inversion H. subst. auto.
Qed.

Module TVAR_EQUALITY <: BOOL_EQUALITY_TYPE.
  Definition t := tvar.
  Definition beq := beq_tvar.
  Definition beq_true := beq_tvar_true_iff.
End TVAR_EQUALITY.

Module TVAR_MAP := EMAP_BOOL TVAR_EQUALITY.


 
