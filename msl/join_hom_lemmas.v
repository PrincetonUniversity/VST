(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.
Require Import msl.psepalg.

(* This file defines a series of lemmas for proving functions from the carrier set
   of one SA to the carrier set of another are join homomorphisms, and then shows
   that some simple properties of SA elems, like identity, comparability, etc.,
   are preserved by join homs.  The idea is due to Rob.
*)

(* Two-argument join homomorphisms *)
Section join_hom2.
  Variables (A B C: Type)
            (JA: Join A)
            (JB: Join B) 
            (JC: Join C) 
            (f: A -> B -> C).

  Definition join_hom2 := forall (a1 a2 a3: A)(b1 b2 b3: B),
      join a1 a2 a3
      -> join b1 b2 b3
      -> join (f a1 b1) (f a2 b2) (f a3 b3).

  (* Two-argument join homomorphisms with a dummy argument *)
  Definition join_hom2' := forall (a1 a2 a3: A)(b1 b2 b3: B),
      join a1 a2 a3
      -> join (f a1 b1) (f a2 b2) (f a3 b3).
End join_hom2.

Implicit Arguments join_hom2 [A B C JA JB JC].
Implicit Arguments join_hom2' [A B C JA].

(* [id] is join hom *)
  Lemma join_hom_id (A: Type) (JA: Join A) : join_hom (fun x => x).
  Proof. unfold join_hom; auto. Qed.

(* Product SA
   Join hom functions on products *)
Section join_hom_prod.
  Variables (A A' B B': Type)
            (JA: Join A) (JA': Join A') 
            (JB: Join B)  (JB': Join B')
            (f: A -> A') (g: B -> B')
            (join_hom_f: join_hom f)
            (join_hom_g: join_hom g).

  Lemma join_hom2_pair: join_hom2 (fun a b => (f a, g b)).
  Proof. firstorder. Qed.

  Lemma join_hom2_pair' : join_hom2 (fun (a: A) (b: B) => (a, b)).
  Proof. firstorder. Qed.

  (* The function from [(a,b)] to [(a',b')] *)  
  Lemma join_hom_prod : join_hom (fun p => (f (fst p), g (snd p))).
  Proof. unfold join_hom; firstorder. Qed.

  (* The function from [a] to [(a', e)] *)
  Lemma join_hom_prodA 
    : forall e: B', join e e e -> join_hom (fun a :A => (f a, e)).
  Proof.
    unfold join_hom in *; intros; simpl; split; auto.
    simpl; auto.
  Qed.

  Lemma join_hom_prodA'
    : forall e: B, join e e e -> join_hom (fun a :A'  => (a, e)).
  Proof.
    unfold join_hom in *; split; simpl; auto.
  Qed.

  (* The function from [b] to [(e, b')] *)
  Lemma join_hom_prodB
    : forall e: A', join e e e -> join_hom (fun b: B => (e, g b)).
  Proof.
    unfold join_hom in *; split; simpl; auto.
  Qed.

  Lemma join_hom_prodB'
    : forall e: A, join e e e -> join_hom (fun b : B' => (e, b)).
  Proof.
    unfold join_hom in *; simpl; split; auto.
  Qed.

  (* Projections are join hom. *)
  Lemma join_hom_proj1
    : join_hom (fun p: A*B => fst p).
  Proof. unfold join_hom; firstorder. Qed.

  Lemma join_hom_proj2
    : join_hom (fun p : A*B => snd p).
  Proof. unfold join_hom; firstorder. Qed.
End join_hom_prod.

Implicit Arguments join_hom2_pair [A A' B B' JA JA' JB JB'].
Implicit Arguments join_hom2_pair' [A B JA JB].
Implicit Arguments join_hom_prodA [A B' JA JB'].
Implicit Arguments join_hom_prodA' [A' B JA' JB].
Implicit Arguments join_hom_prodB [A' B JA' JB].
Implicit Arguments join_hom_prodB' [A B' JA JB'].
Implicit Arguments join_hom_proj1 [A B JA JB].
Implicit Arguments join_hom_proj2 [A B JA JB].

(* Disjoint Sum SA *)
Section join_hom_disjoint_sum.
  Variables (A A' B B': Type)
            (JA: Join A) (JA': Join A')
            (JB: Join B) (JB': Join B')
            (f: A -> A') (g: B -> B')
            (join_hom_f: join_hom f)
            (join_hom_g: join_hom g).
(*
   Definition saAorB := sa_sum saA saB.
  Definition saA'orB' := sa_sum saA' saB'.
*)
  Lemma join_hom_sum
    : join_hom (fun s: A+B => 
        match s with
          | inl x => inl _ (f x)
          | inr y => inr _ (g y)
        end).
  Proof. 
    unfold join_hom.
    destruct x; destruct y; destruct z; firstorder.
  Qed.

  Lemma join_hom_sum_l
    : join_hom (fun s: A+B => 
        match s with
          | inl x => inl _ (f x)
          | inr y => inr _ y
        end).
  Proof. 
    unfold join_hom.
    destruct x; destruct y; destruct z; firstorder.
  Qed.

  Lemma join_hom_sum_r
    : join_hom (fun s: A+B => 
        match s with
          | inl x => inl _ x
          | inr y => inr _ (g y)
        end).
  Proof. 
    unfold join_hom.
    destruct x; destruct y; destruct z; firstorder.
  Qed.

  Lemma join_hom_inj_l
    : join_hom (fun a : A=> inl Void (f a)).
  Proof. firstorder. Qed.

  Lemma join_hom_inj_r
    : join_hom (fun b => inr Void (g b)).
  Proof. firstorder. Qed.

  (* Bijection between [A+unit] and [option A], for convenience later on *)
  Definition sa_sum_option (s: A+unit): option A :=
    match s with 
      | inl s' => Some s'
      | inr _ => None
    end.

  Definition option_sa_sum (s: option A): A+unit := 
    match s with
      | Some s' => inl _ s'
      | None => inr _ tt
    end.

  Lemma sa_sum__option: forall s, sa_sum_option (option_sa_sum s) = s.
  Proof. destruct s; firstorder. Qed.

  Lemma option__sa_sum: forall s, option_sa_sum (sa_sum_option s) = s.
  Proof. destruct s; firstorder; destruct u; firstorder. Qed.

  Definition bij_sa_sum_option : bijection (A+unit) (option A) :=
    Bijection _ _ sa_sum_option option_sa_sum sa_sum__option option__sa_sum.    
End join_hom_disjoint_sum.

(* List SA *)
Section join_hom_list.
  Variables (A: Type) (JA: Join A).

  Lemma join_hom_list_nil
    : join_hom (fun a => a :: nil).
  Proof. 
    unfold join_hom; 
      solve [constructor; auto || constructor].
  Qed.

  Lemma join_hom2_list_cons
    : join_hom2 (fun a l => a :: l).
  Proof.
    unfold join_hom2; constructor; auto.
  Qed.
End join_hom_list.

(* FPMs
   This section proves a join hom lemma specialized to finite partial maps
   producing [option]s.
*)
Section join_hom_fun.
  Variables (Key A: Type)
            (Key_dec_eq: forall k1 k2: Key, {k1=k2}+{~k1=k2})
            (JA: Join A).
(*  
  Definition saKey := sa_equiv Key.
  Definition saKeyA := sa_prod saKey saA.
  Definition saKeyAList := sa_list saKeyA.
  Definition saSum := sa_sum saA sa_unit.
  Definition saRange := sa_bijection _ _ (bij_sa_sum_option A) _ saSum.
*)

  Fixpoint lookup k (rho: list (Key*A)) :=
    match rho with
      | nil => None
      | (k', a) :: rho' => 
          if Key_dec_eq k k' then Some a else lookup k rho'
    end.

  Instance Join_Key : Join Key := @Join_equiv Key.

  Lemma join_hom_fun 
    : join_hom (fun env k => lookup k env).
  Proof.
    unfold join_hom; intros x y z H. 
    induction H.

    (* env is nil *)
    simpl; auto. intro. constructor. 

    (* env is cons *)
    simpl; intro x0.
    destruct x as [k1 a1]; destruct y as [k2 a2]; destruct z as [k3 a3].
    destruct H. simpl in *. destruct H. subst k2 k3.
    destruct (Key_dec_eq x0 k1); auto. constructor; auto.
  Qed.
End join_hom_fun.
Implicit Arguments lookup [Key A].

Lemma join_hom_bij {A: Type} `{Perm_alg A}
            {B: Type}
          (bij: bijection A B):
       @join_hom _ _ _ (Join_bij _ _ _ bij) (bij_f _ _ bij).
  Proof.
    unfold join_hom. intros. do 3 red.
    repeat rewrite bij_gf. auto.
  Qed.

(* Some simple properties preserved by join homs *)
  Lemma join_hom_join_sub {A}{B}`{Join A}`{Join B}:
     forall (f: A -> B) a1 a2, join_sub a1 a2 -> join_hom f -> join_sub (f a1) (f a2).
  Proof. 
    intros.
    destruct H1 as [b H1].
    exists (f b).  auto.
  Qed.

  Lemma join_hom_identity  {A}{B}`{Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}`{Perm_alg B}{SB: Sep_alg B}{CB: Canc_alg B}:
      forall (f: A -> B) a1, identity a1 -> join_hom f -> identity (f a1).
  Proof.
    intros.
    rewrite identity_unit_equiv in H1.
    rewrite identity_unit_equiv.
    unfold unit_for in *. auto.
  Qed.

  Lemma join_hom2_identity  {A}{B}{C}
          `{Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}
          `{Perm_alg B}{SB: Sep_alg B}{CB: Canc_alg B}
          `{Perm_alg C}{SC: Sep_alg C}{CC: Canc_alg C}:
   forall (g: A -> B -> C) a1 b1,
      identity a1 -> identity b1 -> join_hom2 g -> identity (g a1 b1).
  Proof. 
   intros.
    unfold join_hom2 in *.
    rewrite identity_unit_equiv in H2.
    rewrite identity_unit_equiv in H3.
    rewrite identity_unit_equiv.
    unfold unit_for in *. auto.
  Qed.

  Lemma join_hom_comparable {A}{B}`{Perm_alg A}{SA: Sep_alg A}`{Perm_alg B}{SB:Sep_alg B}:
      forall (f: A -> B) a1 a2, comparable a1 a2 -> join_hom f -> comparable (f a1) (f a2).
  Proof.
    intros.
    unfold join_hom in *.
    destruct (comparable_common_unit H1) as [e [? ?]].
    apply common_unit_comparable.
    exists (f e); split; auto.
  Qed.

  Lemma join_hom2_comparable {A}{B}{C}
          `{Perm_alg A}{SA: Sep_alg A}`{Perm_alg B}{SB: Sep_alg B}`{Perm_alg C}{SC: Sep_alg C}:
   forall (g: A -> B -> C) a1 a2 b1 b2,
     comparable a1 a2 
      -> comparable b1 b2 
      -> join_hom2 g
      -> comparable (g a1 b1) (g a2 b2).
  Proof.
    intros.
    unfold join_hom2 in *.
    destruct (comparable_common_unit H2) as [ea [? ?]].
    destruct (comparable_common_unit H3) as [eb [? ?]]. 
    apply common_unit_comparable.
    exists (g ea eb); auto.
  Qed.

(* EXamples: *)

(*  This example doesn't make so much sense, as "comparable" 
  is not so well-defined for Pos_algs 
(* Finite Partial Maps from [nat]s to [option]s *)
Section fpm_ex.
  Variables (A: Type)
            (JA: Join A) (saA: Pos_alg A)(CA: Canc_alg A)
            (a b: A)
            (l: list (nat*A)).

  Definition mkEnv := fun p:nat*A => p :: l.
  Definition env1 := mkEnv (1%nat, a).
  Definition env2 := mkEnv (1%nat, b).
  Definition fpm (env: list (nat*A)) := fun k:nat => lookup eq_nat_dec k env.

Check Sep_sum.


 Definition saOption := Perm_bij _ _ _ _ (bij_sa_sum_option A).
  Definition saB := Perm_fun nat _ _ saOption.
  Local Instance Join_nat : Join nat := @Join_equiv nat.
  Local Instance Sep_nat : Sep_alg nat := Sep_equiv nat.

  Local Instance Canc_B : Canc_alg (nat -> option A).
  Proof. auto with typeclass_instances. Qed.

  Lemma fpm_comparable_ex
    : comparable (fpm env1) (fpm env2).
  Proof.
    simpl.

Check (@join_hom_comparable (list (nat*A)) _ _ _ _ _ fpm).
Print join_hom_comparable.
A, B, J, H,  J0, H0

    apply join_hom_comparable with (f := fpm).

; [ | apply join_hom_fun; auto].
    eapply join_hom2_comparable.
    eapply join_hom2_comparable with (g := fun a b => (a,b)).
    eapply comparable_refl.
    eapply H.
    eapply join_hom2_pair'.
    eapply comparable_refl.
    eapply join_hom2_list_cons.
Qed.

End fpm_ex.
*)
