(*  Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* An axiomatization of expected polynomial time as a type class.  *)

Require Import FCF.Crypto.
Require Import FCF.Asymptotic.
Require Import FCF.FCF.

Definition procedure_family(A : nat -> Type) := forall n, A n.
Definition efficiency_predicate := forall (A : nat -> Type), procedure_family A -> Prop.

(* We can abstract over arrow.  This would allow us to make sure that there is a model of the axioms below. *)
(* Is there a language with a "function space" and "efficiency" that satisfies these semantics.  Make this language! *)
(* Exercise: write the description of this class in a paper. *)

Class expected_poly_time_predicate(efficient : efficiency_predicate) := {

  expected_poly_time_compose : 
  forall (A B C : nat -> Type)(f1 : forall n, A n -> B n)(f2 : forall n, A n -> B n -> C n),
    efficient _ f1 ->
    efficient _ f2 ->
    efficient _ (fun n (a : A n) => f2 n a (f1 n a));

  expected_poly_time_compose_0 : 
    forall (A B : nat -> Type)(f1 : forall n, A n)(f2 : forall n, A n -> B n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n => f2 n (f1 n));

  expected_poly_time_ident : 
    forall (A : nat -> Type),
      efficient _ (fun n (a : A n) => a);

  expected_poly_time_const : 
    forall (A B : nat -> Type)(b : forall n, B n),
      efficient _ b ->
      efficient _ (fun (n : nat)(_ : A n) => (b n));

  expected_poly_time_closure_const : 
    forall (A : Type)(a : A)(B : nat -> Type)(f : forall n, A -> B n),
      efficient _ f ->
      efficient _ (fun (n : nat) => @f n a);

  expected_poly_time_nil : 
    forall (A : nat -> Type),
      efficient _ (fun n => @nil (A n));
  
  expected_poly_time_cons : 
  forall (A : nat -> Type),
    efficient _ (fun n (a : A n) ls => cons a ls);

  expected_poly_time_pair : 
    forall (A : nat -> Type)(B : nat -> Type),
      efficient _ (fun n => @pair (A n) (B n));

  expected_poly_time_ret : 
    forall (A : nat -> Set)(eqd : forall n, eq_dec (A n)),
      efficient _ (fun n (a : A n) => Ret (eqd n) a);

  expected_poly_time_rnd : 
  forall f,
    polynomial f ->
    efficient _ (fun n => ({0, 1}^(f n)));

  expected_poly_time_bind : 
  forall (A B : nat -> Set),
    efficient _ (fun n => @Bind (A n) (B n));

  expected_poly_time_vec_hd : 
    forall (A : nat -> Type) z,
      efficient _ (fun n (v : Vector.t (A n) (S z)) => Vector.hd v);

   expected_poly_time_pair_arg : 
    forall (A B C: nat -> Type)(f : forall (n : nat), A n -> B n -> C n),
      efficient _ (fun (n : nat)(p : (A n * B n)) => f n (fst p) (snd p)) ->
      efficient _ f;

  expected_poly_time_unpair_arg : 
    forall (A B C: nat -> Type)(f : forall (n : nat), (A n * B n) -> C n),
      efficient _ (fun (n : nat)(a : A n)(b : B n) => f n (a, b)) ->
      efficient _ f;

      (* The let rules are structured differently -- I should see if I can make them consistent *)
  expected_poly_time_let_3_f : 
    forall (A B C D E: nat -> Type)(f1 : forall n, (A n) -> (B n * C n * D n))(f2 : forall n, (A n) -> B n -> C n -> D n -> E n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => [x1, x2, x3] <-3 (f1 n a); f2 n a x1 x2 x3);

  expected_poly_time_let_2_f : 
    forall (A B C E: nat -> Type)(f1 : forall n, (A n) -> (B n * C n))(f2 : forall n, (A n) -> B n -> C n -> E n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => [x1, x2] <-2 (f1 n a); f2 n a x1 x2);

  expected_poly_time_let_f : 
    forall (A : nat -> Type)(B : nat -> Set)(C : nat -> Type)(f1 : forall n, (A n) -> B n)(f2 : forall n, (A n) -> B n -> C n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => x <- (f1 n a); f2 n a x);

  expected_poly_time_fst : 
    forall (A B : nat -> Type),
      efficient _ (fun n (a : A n * B n) => fst a);

  expected_poly_time_snd : 
    forall (A B : nat -> Type),
      efficient _ (fun n (a : A n * B n) => snd a);
  
  expected_poly_time_if : 
    forall (A : nat -> Type),
      efficient _ (fun n (b : bool)(a1 a2 : A n) => if b then a1 else a2);
  
  expected_poly_time_bvxor : 
    efficient _ BVxor;
  
  expected_poly_time_eqb_bool : 
    efficient _ (fun n (x y : bool) => eqb x y)

}.

Section expected_poly_time_theory.

  Context `{ept : expected_poly_time_predicate}.

  Theorem expected_poly_time_compose_simp : 
    forall (A B C : nat -> Type)(f1 : forall n, A n -> B n)(f2 : forall n, B n -> C n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => f2 n (f1 n a)).
    
    intuition.
    eapply (@expected_poly_time_compose _ _ _ _ _ _ (fun n a b => (f2 n b))); eauto.
    eapply expected_poly_time_const; eauto.

  Qed.

  Theorem expected_poly_time_compose_binary : 
    forall (A B C D : nat -> Type)(f1 : forall n, A n -> B n)(f2 : forall n, A n -> C n)(f3 : forall n, B n -> C n -> D n) ,
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ f3 -> 
      efficient _ (fun n (a : A n) => f3 n (f1 n a) (f2 n a)).
    
    intuition.
    eapply (@expected_poly_time_compose _ _ _ _ _ _ (fun n a b => f3 n (f1 n a) b)); eauto.
    eapply (@expected_poly_time_compose _ _ _ _ _ _ (fun n a b => f3 n b)); eauto.
    eapply expected_poly_time_const.
    eauto.
    
  Qed.


  Theorem expected_poly_time_pair_f : 
    forall (A B C : nat -> Type)(f1 : forall n, A n -> B n)(f2 : forall n, A n -> C n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => (f1 n a, f2 n a)).
    
    intuition.
    eapply (@expected_poly_time_compose_binary _ _ _ _ _ _ (fun n b c => pair b c)); eauto.
    eapply expected_poly_time_pair.
  Qed.

  Theorem expected_poly_time_bvxor_f : 
    forall (A : nat -> Type)(f1 : forall n, A n -> Bvector n)(f2 : forall n, A n -> Bvector n),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => BVxor n (f1 n a) (f2 n a)).
    
    intuition.
    eapply (@expected_poly_time_compose_binary _ _ _ _ _ _ BVxor); eauto.
    eapply expected_poly_time_bvxor.
  Qed.

  Theorem expected_poly_time_eqb_bool_f : 
    forall (A : nat -> Type)(f1 : forall n, A n -> bool)(f2 : forall n, A n -> bool),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => eqb (f1 n a) (f2 n a)).
    
    intuition.
    eapply (@expected_poly_time_compose_binary _ _ _ _ _ _ (fun n a b => eqb a b)); eauto.
    eapply expected_poly_time_eqb_bool.
  Qed.

  Theorem expected_poly_time_fst_f : 
    forall (A B C : nat -> Type)(f : forall n, A n -> (B n * C n)),
      efficient _ f ->
      efficient _ (fun n (a : A n) => fst (f n a)).
    
    intuition.
    eapply (@expected_poly_time_compose_simp _ _ _ _ (fun n a => fst a)); eauto.
    eapply expected_poly_time_fst.
  Qed.
  
  Theorem expected_poly_time_snd_f : 
    forall (A B C : nat -> Type)(f : forall n, A n -> (B n * C n)),
      efficient _ f ->
      efficient _ (fun n (a : A n) => snd (f n a)).
    
    intuition.
    eapply (@expected_poly_time_compose_simp _ _ _ _ (fun n a => snd a)); eauto.
    eapply expected_poly_time_snd.
  Qed.

  Theorem expected_poly_time_compose_0_binary : 
    forall (A B C : nat -> Type)(f1 : forall n, A n)(f2 : forall n, B n)(f3 : forall n, A n -> B n -> C n) ,
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ f3 -> 
      efficient _ (fun n => f3 n (f1 n) (f2 n)).
    
    intuition.
    eapply (@expected_poly_time_compose_0 _ _ _ _ _ (fun n b => f3 n (f1 n) b)); eauto.
    eapply (@expected_poly_time_compose_0 _ _ _ _ _ (fun n b => f3 n b)); eauto.
    
  Qed.

  Theorem expected_poly_time_bind_0_f : 
    forall (A B : nat -> Set) (a : forall n, Comp (A n)) (b : forall n, A n -> Comp (B n)),
      efficient _ a ->
      efficient _ b ->
      efficient _ (fun n => (Bind (a n) (b n))).
    
    intuition.
    eapply (@expected_poly_time_compose_0_binary _ _ _ a b (fun n a b => Bind a b)); eauto.
    eapply expected_poly_time_bind.
  Qed.

  Theorem expected_poly_time_bind_f : 
    forall (A : nat -> Type)(B C : nat -> Set) (b : forall n, A n -> Comp (B n)) (c : forall n, A n -> B n -> Comp (C n)),
      efficient _ b ->
      efficient _ c ->
      efficient _ (fun n a => (Bind (b n a) (c n a))).
    
    intuition.
    eapply (@expected_poly_time_compose_binary _ _ _ _ b c (fun n a b => Bind a b)); eauto.
    eapply expected_poly_time_bind.
  Qed.

  Theorem expected_poly_time_ret_f : 
    forall (A : nat -> Type)(B : nat -> Set)(eqd : forall n, eq_dec (B n))(f : forall n, (A n) -> (B n)),
      efficient _ f ->
      efficient _ (fun n (a : A n) => Ret (eqd n) (f n a)).
    
    intuition.
    eapply (@expected_poly_time_compose_simp _ _ _ _ (fun n b => Ret (eqd n) b)); eauto.
    eapply expected_poly_time_ret.
    
  Qed.

  Theorem expected_poly_time_rnd_ident : 
    efficient _ (fun n => ({0, 1} ^ n)).
    
    eapply expected_poly_time_rnd.
    exists 1%nat.
    exists 1%nat.
    exists 0%nat.
    intuition.
    simpl.
    omega.
  Qed.

  Theorem expected_poly_time_rndbool :
    efficient _ (fun (n : nat) => {0, 1}).
  
    eapply expected_poly_time_bind_0_f.
    
    eapply expected_poly_time_rnd.
    exists 0%nat.
    exists 1%nat.
    exists 0%nat.
    intuition.
    
    eapply expected_poly_time_ret_f.
    eapply expected_poly_time_vec_hd.
    
  Qed.


  Theorem expected_poly_time_if_f : 
    forall (A B: nat -> Type)(f_b : forall n, (A n) -> bool)(f_so f_not : forall n, A n -> B n),
      efficient _ f_b ->
      efficient _ f_so ->
      efficient _ f_not ->
      efficient _ (fun n (a : A n) => if (f_b n a) then (f_so n a) else (f_not n a)).
    
    intuition.
    
    eapply (@expected_poly_time_compose _ _ _ _ _ _ (fun n a (b : bool) => if b then (f_so n a) else (f_not n a))); eauto.
    
    eapply expected_poly_time_pair_arg.
    eapply (@expected_poly_time_compose _ _ _ _ _ _ (fun n (a : A n * bool) b => if (snd a) then b else (f_not n (fst a)))); eauto.
    apply (@expected_poly_time_compose_simp _ _ _ _ f_so); eauto.
    eapply expected_poly_time_fst.
    
    eapply expected_poly_time_pair_arg.
    eapply (@expected_poly_time_compose _ _ _ _ _ _ (fun n (a : A n * bool * B n) b => if (snd (fst a)) then (snd a) else b)); eauto.
    apply (@expected_poly_time_compose_simp _ _ _ _ f_not); eauto.
    apply (@expected_poly_time_compose_simp _ _ _ _ (fun n a => fst a)); eauto.
    eapply expected_poly_time_fst.
    eapply expected_poly_time_fst.
    
    eapply expected_poly_time_unpair_arg.
    eapply expected_poly_time_unpair_arg.
    simpl.
    eapply expected_poly_time_const.
    eapply expected_poly_time_if.    
    
  Qed.

  Theorem expected_poly_time_cons_f : 
    forall A B (f1 : forall n, A n -> B n) (f2 : forall n, A n -> list (B n)),
      efficient _ f1 ->
      efficient _ f2 ->
      efficient _ (fun n (a : A n) => (cons (f1 n a) (f2 n a))).
    
    intuition.
    eapply (@expected_poly_time_compose_binary _ _ _ _ _ _ (fun n a b => cons a b)); intuition.
    eapply expected_poly_time_cons.
  Qed.

End expected_poly_time_theory.

Ltac ept_tac :=
  match goal with
    | [|- ?efficient _ (fun n a => a)] => eapply expected_poly_time_ident
    | [|- ?efficient _ (fun n a => fst a)] => eapply expected_poly_time_fst
    | [|- ?efficient _ (fun n a => snd a)] => eapply expected_poly_time_snd
    | [|- ?efficient _ _ ] => eapply expected_poly_time_rndbool
    | [|- ?efficient _ Rnd ] => eapply expected_poly_time_rnd_ident
    | [|- ?efficient _ (fun n => nil)] => eapply expected_poly_time_nil
      
    | [|- ?efficient _ _ ] => eapply expected_poly_time_if_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_eqb_bool_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_bvxor_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_cons_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_pair_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_fst_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_snd_f
    | [|- ?efficient _ (fun n a => ?b)] => eapply expected_poly_time_const
    | [|- ?efficient _ _] => eapply expected_poly_time_closure_const
    | [|- ?efficient _ _ ] => eapply expected_poly_time_ret_f
    | [|- ?efficient _ (fun n => Bind _ _) ] => eapply expected_poly_time_bind_0_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_bind_f
    | [|- ?efficient _ _ ] => eapply expected_poly_time_pair_arg
  end.

Ltac ept := repeat ept_tac.
  
