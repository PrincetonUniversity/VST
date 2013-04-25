Require Import AST.
Require Import Coqlib.
Require Import Memory.
Require Import Values.
Require Import Integers.
Require Import Events.

Require Import sepcomp.extspec.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.mem_lemmas.

Definition is_ptr (v: val) := exists b ofs, v = Vptr b ofs.

(* can't define as a fixpoint because there may be cycles *)

Inductive ptr_closure (b: block) (ofs: Z) (m: mem): block -> Z -> Prop :=
| ptr_closure_base: forall ofs', ptr_closure b ofs m b ofs'
| ptr_closure_trans: forall b'' ofs'' b' ofs',
  Mem.load Mint32 m b ofs = Some (Vptr b'' ofs'') -> 
  ptr_closure b'' (Int.intval ofs'') m b' ofs' -> 
  ptr_closure b ofs m b' ofs'.

Definition closure (v: val) (m: mem): val -> Prop :=
  fun v': val => match v, v' with 
                   | Vptr b ofs, Vptr b' ofs' => 
                     ptr_closure b (Int.intval ofs) m b' (Int.intval ofs')
                   | _, _ => False
                 end.

Definition val_not_reserved (v: option val) (m: mem) (r: reserve) :=
  match v with Some v' => 
    forall b ofs, closure v' m (Vptr b ofs) -> ~r b (Int.intval ofs)
  | None => True
  end.

Lemma val_not_reserved_base: 
  forall b ofs m r,
  val_not_reserved (Some (Vptr b ofs)) m r -> 
  ~r b (Int.intval ofs).
Proof.
intros b ofs m r NR.
hnf in NR.
specialize (NR b ofs).
intros CONTRA.
destruct NR.
solve[econstructor].
solve[auto].
Qed.

(*TODO: move elsewhere*)
Definition val_valid_opt (v: option val) (m: mem) :=
  match v with
  | None => True
  | Some v' => val_valid v' m
  end.

Definition reserve_separated1 (r r': reserve) m := 
  forall b ofs, ~r b ofs -> r' b ofs -> ~Mem.valid_block m b.

Section compile_safety.
  Context {G C D Z: Type}.
  Context (Hcore: EffectfulSemantics G C D).

  Variable ge: G.

  CoInductive compile_safe: Z -> reserve -> C -> mem -> Prop :=
  | compile_safe_halt: 
    forall z r c m ret, 
      safely_halted Hcore c = Some ret -> 
      val_not_reserved (Some ret) m r -> 
      val_valid ret m -> 
      compile_safe z r c m
  | compile_safe_step:
    forall z (r: reserve) c m c' m',
      corestep Hcore ge c m c' m' -> 
      (forall c' m', 
        guarantee Hcore r c m -> 
        corestep Hcore ge c m c' m' -> 
        guarantee Hcore r c' m' /\ 
        forall r': reserve, 
          guarantee Hcore r' c' m' -> 
          compile_safe z r' c' m') -> 
      compile_safe z r c m
  | compile_safe_external: 
    forall z (r: reserve) c m e sig args, 
      at_external Hcore c = Some (e, sig, args) -> 
      (forall v, In v args -> val_not_reserved (Some v) m r /\ val_valid v m) -> 
      (forall (z': Z) (r': reserve) m' ret c',
        reserve_incr r r' -> 
        reserve_separated1 r r' m -> 
        val_not_reserved ret m' r' -> 
        val_valid_opt ret m' -> 
        after_external Hcore ret c = Some c' -> 
        compile_safe z' r' c' m') ->  
    compile_safe z r c m.

  Fixpoint compile_safeN (n:nat) (z:Z) (r:reserve) (c:C) (m:mem) : Prop :=
    match n with
    | O => True
    | S n' => 
       match at_external Hcore c, safely_halted Hcore c with
       | None, None =>
           forall c' m', 
             corestep Hcore ge c m c' m' -> 
             guarantee Hcore r c' m' /\ compile_safeN n' z r c' m'
       | Some (e,sig,args), None =>
         (forall v, In v args -> val_not_reserved (Some v) m r /\ val_valid v m) -> 
         forall ret m' z' (r': reserve) c',
           reserve_incr r r' -> 
           reserve_separated1 r r' m -> 
           val_not_reserved ret m' r' -> 
           after_external Hcore ret c = Some c' ->
           compile_safeN n' z' r' c' m'
       | None, Some ret => val_not_reserved (Some ret) m r
       | Some _, Some _ => False
       end
    end.

  Definition compile_safe' z r c m := forall n, compile_safeN n z r c m.

  Definition corestep_fun  :=
       forall ge m q m1 q1 m2 q2 ,
       corestep Hcore ge q m q1 m1 -> 
       corestep Hcore ge q m q2 m2 -> 
       (q1, m1) = (q2, m2).

(*  Lemma compile_safe_safe': 
    forall z r c m,
    corestep_fun -> 
    compile_safe z r c m -> compile_safe' z r c m.
  Proof.
  intros until m; intros FUN H1 n.
  revert z r c m H1.
  induction n; intros; hnf; auto.
  case_eq (at_external Hcore c).
  intros [[ef sig] args] H2.
  case_eq (safely_halted Hcore c).
  intros v H3.
  exploit @at_external_halted_excl.
  instantiate (1 := c).
  instantiate (1 := Hcore).
  rewrite H2, H3.
  intros [?|?]; congruence.
  intros NONE.
  intros.
  apply IHn.
  inv H1; try solve[congruence].
  apply corestep_not_at_external in H6.
  congruence.
  solve[eapply H6; eauto].
  intros NONE.
  case_eq (safely_halted Hcore c).
  intros v HALT.
  inv H1; try solve[congruence].
  solve[rewrite H in HALT; inv HALT; auto].
  exploit @corestep_not_halted; eauto; intros.
  congruence.
  intros NONE'.
  intros until m'; intros H2.
  inv H1; try solve[congruence].
  generalize (FUN _ _ _ _ _ _ _ H2 H0); intros X.
  solve[inv X; split; auto].
  Qed.*)

  Lemma compile_safe'_corestep_forward:
    forall c m c' m' n z r,
    corestep Hcore ge c m c' m' -> 
    compile_safeN (S n) z r c m -> 
    guarantee Hcore r c' m' /\ compile_safeN n z r c' m'.
  Proof.
  simpl; intros.
  erewrite corestep_not_at_external in H0; eauto.
  erewrite corestep_not_halted in H0; eauto.
  Qed.

  Lemma compile_safe_corestep_forward:
    forall c m c' m' z r,
    compile_safe z r c m -> 
    guarantee Hcore r c m -> 
    corestep Hcore ge c m c' m' -> 
    guarantee Hcore r c' m' /\ 
    (forall r': reserve, 
      guarantee Hcore r' c' m' -> 
      compile_safe z r' c' m').
  Proof.
  simpl; intros until r; intros.
  generalize H1 as H'; intro.
  generalize H1 as H''; intro.
  apply corestep_not_at_external in H'.
  apply corestep_not_halted in H''.
  inv H; try solve[congruence].
  destruct (H3 _ _ H0 H1).
  solve[split; auto].
  Qed.

  Lemma compile_safe_downward1 :
    forall n c m z r,
      compile_safeN (S n) z r c m -> compile_safeN n z r c m.
  Proof.
    induction n; simpl; intros; auto.
    destruct (at_external Hcore c);
      destruct (safely_halted Hcore c).
    destruct p; auto.
    destruct p. destruct p.
    intros.
    exploit H; eauto.
    auto.
    intros.
    exploit H; eauto.
    intros [? ?].
    solve[split; auto].
  Qed.

  Lemma compile_safe_downward: 
    forall n n' c m z r,
      le n' n ->
      compile_safeN n z r c m -> compile_safeN n' z r c m.
  Proof.
    do 7 intro. revert c m z r. induction H; auto.
    intros. apply IHle. apply compile_safe_downward1. auto.
  Qed.
    
End compile_safety.


