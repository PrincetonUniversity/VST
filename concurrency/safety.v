(** *Notice: This file is very sketchy at the moment. Read at your own risk.*)


From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
      
Require Import Coq.ZArith.ZArith.

Require Import compcert.common.Memory.

(*Require Import concurrency.juicy_machine.

Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.*)
Require Import msl.eq_dec.

Require Import concurrency.konig.

Section cardinality.
(*Here goes cardinality stuff*)
End cardinality.

Section filtered_konig.  
  Variable X: Type.
  Axiom X_dec: forall x y:X, {x=y} + {x<>y}.
  Variable Filter: X -> Prop.
  Variable R: X->X->Prop.
  Axiom  preservation :  forall P P', Filter P -> R P P' -> Filter P'.
  
  Record TT :Type:= mkTT {thing: X; prf: Filter thing}.
  Inductive RR: TT->TT->Prop:=
  | stepstep: forall P x' (stp: R (thing P) x'), RR P (mkTT x' (preservation _ _ (prf P) stp)).
  
  Lemma filtered_to_unfiltered_safe:
    forall P,
      konig.safe _ RR P ->
      konig.safe X R (thing P).
  Proof.
    cofix.
    move => P sf.
    inversion sf; subst x.
    inversion H; subst P0.
    apply: (safe_cons _ _ (thing P) x'0 stp).
    replace x'0 with (thing x').
    by apply: filtered_to_unfiltered_safe.
    by rewrite -H2.
  Qed.
  Lemma unfiltered_to_filtered_safeN:
    forall n P,
      konig.safeN X R n (thing P) ->
      konig.safeN _ RR n P.
  Proof.
    induction n.
    - constructor.
    - move=> P sf.
      inversion sf.
      apply: (safeS _ _ n P (mkTT x' (preservation _ _ (prf P) H0)))=> /=.
      by constructor.
      by apply: IHn.
  Qed.

  Inductive cardinality {X} (P:X->Prop): nat -> Prop:=
  |Cardinality n (f:nat-> X): (forall i j, i<n -> j<n -> i<>j -> f(i)<>f(j)) ->
                           (forall i, i<n -> P (f i)) ->
                           (forall x, P x -> exists i, i < n /\ f i = x) ->
                           cardinality P n.
  Inductive cardinality' {X} (P:X->Prop): nat -> Prop:=
  |Cardinality' n (f:nat-> X): (forall i j, i<n -> j<n -> i<>j  -> f(i)<>f(j)) ->
                            (forall i, i<n -> P (f i)) ->
                            cardinality' P n.

  Lemma repetition_dec: forall (f:nat -> X) x n,  (exists i, i<n /\ f(i) = x) \/ (forall i, i<n -> f i <> x).
              Proof. 
                induction n=>//.
                - constructor 2 => //.
                - move: IHn=> [[]i [] A B| A].
                  + constructor; exists i; split =>//; auto.
                  + destruct (X_dec (f n) x).
                    * left; exists n; split=> //.
                    * right=> i ineq.
                      { destruct (Nat.eq_dec i n).
                        - subst i => //.
                        - apply: A=>//.
                          destruct (le_lt_dec n i) as [HH|HH]; move: HH=> /leP // /leP ineq2.
                        contradict n1. move: ineq=> /leP ineq.
                        omega.
                      }
              Qed.
  Lemma finite_cardinality:
    forall (P:X->Prop) (EM: forall x, P x \/ ~ P x), finite P -> exists n, cardinality P n. 
  Proof.
    move => P EM [] n [] f FIN.
    cut (forall n2,
            (exists f0 n0,
                (n0 <= n2) /\
               (forall i j, i<n0 -> j<n0 -> i <> j -> f0(i)<>f0(j)) /\
               (forall i, i<n0 -> P (f0 i)) /\
               (forall i, i<n2 -> P (f i) -> exists i0, i0<n0 /\ f i = f0 i0)) \/
               (exists n1, n1<=n2 /\ cardinality P n1)
        ).
    { move => HH; move: (HH n) => [ [] f0 [] n0 [] A [] B []  C D | [] n0 [] HH0 HH1 ].
      - exists n0; exists f0 => //.
        move =>  x Px. move: (FIN x Px)=> [] i [] /leP /D D' fi.
        move: Px; rewrite -fi => /D' [] i0 [] ineqi0 fifi0. rewrite fifi0. 
        by exists i0; split.
      - by exists n0.
    }
    { induction n2. 
      - left; exists f, 0; repeat split=>//.
      - move: IHn2=> [].
        + move => [] f0 [] n0 [] ineq02 [] inject0 [] prf0 subset.
          destruct (Compare.le_or_le_S n n2) as [A | A]; move:A=> /leP ineq.
          * right. exists n0; split => //; auto.
            apply: (Cardinality P n0 f0)=> //.
            move=> x Px. move: (FIN x Px)=> [] i [] /leP ineq' fi.
            assert (H:i< n2) by admit.
            move: Px; rewrite -fi=> /(subset _ H) []  i' [] ineq0' fifo.
            by rewrite fifo; exists i'; split.
          * { pose (new_x:= f n2).
              (*check if new_x is in P*)
              destruct (EM new_x) as [Pnew_x | nPnew_x].
              - left; destruct (repetition_dec f new_x n2) as [HH|HH]; move: HH.
                + move=> [] i [] ineq2 fi.
                  exists f0, n0; repeat split=>//; auto.
                  move=> j ineqj Px.
                  destruct (Nat.eq_dec j n2).
                  * subst j.
                    move: Px. rewrite -/new_x -fi => /(subset i ineq2) => [] [] i' [] ineqi' fifi'.
                    by exists i'; split.
                  * apply: subset=>//.
                    destruct (lt_dec j n2) as [HH|HH]; move:HH ineqj=> /leP // /leP HH /leP ineqj.
                    by contradict n1; omega.
                    
                + { move => HH.
                    pose (f0':= eq_dec.upd f0 n0 new_x); exists f0', n0.+1; repeat split => //.
                    - move => i j ineqi ineqj diffij.
                      destruct (Nat.eq_dec i n0);destruct (Nat.eq_dec j n0); try subst=> //.
                      + rewrite /f0' eq_dec.upd_eq eq_dec.upd_neq=> // .
                        assert (Hj: j < n0) by admit.
                        move: (prf0 j Hj) => /FIN [] h [] A B; rewrite -B. 
                        move => eq. apply: (HH h)=> //.
                        admit. (*by integers.*)
                        
                      + rewrite /f0' eq_dec.upd_eq eq_dec.upd_neq=> // .
                        assert (Hj: i < n0) by admit.
                        move: (prf0 i Hj) => /FIN [] h [] A B; rewrite -B. 
                        move => eq. apply: (HH h)=> //.
                        admit. (*by integers.*)
                          by move=>AA; apply: diffij.
                      + rewrite /f0' eq_dec.upd_neq=>//; auto;
                        rewrite eq_dec.upd_neq=>//; auto.
                        assert (ineqi':  i < n0) by admit.
                        assert (ineqj':  j < n0) by admit.
                          by move: inject0 => /(_ _ _ ineqi' ineqj' diffij).
                    - move=> i0 ineqi0; destruct (Nat.eq_dec i0 n0).
                        by subst; rewrite /f0' eq_dec.upd_eq.
                        rewrite /f0' eq_dec.upd_neq; [apply: prf0| admit].
                        admit.
                    - move => i0 ineq0 Px; destruct (Nat.eq_dec i0 n2).
                        by subst; exists n0; split =>//; rewrite /f0' eq_dec.upd_eq.
                        move: (subset i0)=> [] //. admit.
                        move=> i0' [] A B. exists i0'; split=>//. auto.
                        rewrite /f0' eq_dec.upd_neq=> //. admit.
                  }
                + left; exists f0, n0; repeat split=> //.
                  * auto.
                  * move => i0 ineq0. destruct (Nat.eq_dec i0 n2).
                      by subst; move=> Px; exfalso; apply nPnew_x.
                      assert (H:i0<n2) by admit.
                      by move /(subset _ H).
            }
        + move => [] n0 [] /leP /(le_trans _ _ n2.+1) A B; right; exists n0; split=> //.
          admit.
  Admitted.

  
  Lemma filtered_konigsafe:
    forall (x : X),
      (forall P : Prop, P \/ ~ P) ->
      (forall x0 : X, Filter x0 -> finite (R x0)) ->
      Filter x ->
      (forall n : nat, safeN X R n x) -> konig.safe X R x.
  Proof.
    move => x EM blah inF sfN.
    replace x with (thing (mkTT x inF)) by reflexivity.
    eapply filtered_to_unfiltered_safe.
    eapply concurrency.konig.konigsafe => //.

    move=> [] xx prfx.
    rewrite /finite.

    assert (EM': forall x0, R xx x0 \/ ~ R xx x0) by (move=>x0; apply EM;auto).
    move: (blah _ prfx)=> /(finite_cardinality _ EM') [] n car.
    inversion car; subst n0.

    exists n.
    assert (HH: forall i, i < n -> Filter (f i)) by move => i / H0 / (preservation _ _ prfx) //.
    assert (refl:forall i n, (i < n)%coq_nat -> is_true (i < n)) by move => i' n' /ltP //. 
    pose (f0:= fun i =>
                 match le_lt_dec n i with
                 | left _ =>  mkTT xx prfx
                 | right ineq => mkTT (f i) (HH i (refl i n ineq))
                 end ).
    
    exists f0 => [] [] xx' prfx' /= stepstep. inversion stepstep.
    move: stp0; subst x'=> /= /H1 [] i0 [] /ltP A B.
    exists i0; split=> //.
    rewrite /f0.
    destruct (le_lt_dec n i0) => //.
    move: A l=> /ltP A /leP.
    admit.
    clear stepstep.
    remember (HH i0 (refl i0 n l)) as prfx''. clear Heqprfx''.
    move: prfx' prfx''. 
    dependent rewrite B => P1 P2; f_equal.
    apply: ProofIrrelevance.PI.proof_irrelevance.

    move => n.
    apply: unfiltered_to_filtered_safeN=> //.
  Admitted.

End filtered_konig.

Section Safety.
  Context (ST:Type)(SCH:Type).
  Context (STEP:ST->SCH->ST->SCH-> Prop).
  Context (valid: ST-> SCH -> bool).
  
  Axiom schedule_dec:
    forall (U U':SCH), {U=U'} + {U<>U'}.
  
  Inductive ksafe (st:ST) U: nat -> Prop :=
  |sft0: ksafe st U 0
  |sft_step: forall n st' U', STEP st U st' U' -> (forall U'', valid st' U'' -> ksafe st' U'' n) -> ksafe st U (S n).

  CoInductive safe st U: Prop:=
  | csft_step: forall st' U', STEP st U st' U' -> (forall U'', valid st' U'' -> safe st' U'') -> safe st U.

  (*The proof relies on the sets of states: SST's*)
  Definition SST:= ST -> Prop.
  Definition is_in (st:ST)(P:SST):= P st. 
  (*Notation enth:= (List.nth_error).*)
  Infix "\In":= (is_in) (at level 20, right associativity).

  (*Generalizes a non-deterministic relation to sets *)
  Inductive SStep {X Y: Type} (R: X -> X -> Y -> Prop)(valid:X->Y->Prop) (P P':X -> Prop) : Prop:=
  | blahblah: (forall x y, P x -> valid x y -> exists x', R x x' y /\ P' x') ->
              (forall x', P' x' -> exists x y, R x x' y /\ P x /\ valid x y) ->
              SStep R valid P P'.
  Definition SST_step : SST -> SST -> Prop := SStep (fun st st' U => exists U', STEP st U st' U') valid.
  
  (*Instantiating koning's variables *)
  Definition SsafeN:= konig.safeN SST SST_step. 
  Definition Ssafe:= konig.safe (SST) SST_step.
  (*Initial state is singleton.*)
  Inductive P_init {st_init:ST}: SST:=
  |ItIsMe: P_init st_init.
  
  Lemma finite_P_init: forall {st}, finite (@P_init st).
  Proof. by move =>st; exists 1, (fun _ => st) => st' []; exists 0; split. Qed.
  
  Lemma SsafeN_ksafe': forall n P,
      SsafeN n P -> forall st U, st \In P -> valid st U -> ksafe st U n.
  Proof.
    induction n.
    - constructor.
    - move=> P HH st U inP VAL. 
      inversion HH; subst.
      inversion H0.
      move: VAL inP => /H H' /H'  [] st' [][] U' STP inx'.
      apply: (sft_step st U n st' U' STP)=> U'' VALID'.
      apply: (IHn x' _ )=>//.
  Qed.
  
  Corollary SsafeN_ksafe: forall n st,
      SsafeN n (@P_init st) -> forall U, valid st U -> ksafe st U n.
  Proof. move=> n st mysN U VAL. apply: (SsafeN_ksafe' n P_init mysN) => //. Qed.
  
  Lemma ksafe_SsafeN': forall n P,
      (forall st U, st \In P -> valid st U -> ksafe st U n) ->
      SsafeN n P.
  Proof.
    induction n.
    - constructor.
    - move=> P HH.
      pose (P':= fun st' => exists st U U',
                     P st /\
                     valid st U /\
                     STEP st U st' U' /\
                     (forall U'', valid st' U'' -> ksafe st' U'' n)).
      apply: (safeS _ _ n P P').
    - constructor.
      + move => st U inP VAL.
        move: (inP) (VAL)=> /HH HH' /HH' ksf.
        inversion ksf.
        exists st'; split; [exists U'| ] =>//.
        rewrite /is_in /P'.
        exists st, U, U'=>//.
      + move => st'.
        rewrite /is_in /P'=> [] [] st [] U [] U' []inP[] VAL[] STP CONDITION.
        exists st, U; split;[exists  U' | ]=>//.
    - eapply IHn => st' U [] st [] UU [] U' [] inP [] VAL [] STP COND;
      by apply: COND.
  Qed.
  
  Lemma ksafe_SsafeN: forall st_init,
      (forall U, valid st_init U) ->
      forall n, (forall U, ksafe st_init U n) ->
           SsafeN n (@P_init st_init).
  Proof.
    move => st_init all_valid n Uksf.
    apply ksafe_SsafeN' => st' U' [] val.
    apply: Uksf.
  Qed.

  Lemma Ssafe_safe': forall P,
      Ssafe P -> forall st U, st \In P -> valid st U -> safe st U.
  Proof.
    cofix=> P SF st U. 
    inversion SF; subst x; rename x' into P'.
    inversion H => /H1 H1' /H1' [] st' [] [] U' STP inP'.
    apply: (csft_step _ _ st' U')=>// U'' VAL'.
    apply: (Ssafe_safe' P')=> //.
  Qed.

  Lemma Ssafe_safe: forall st_init,
      (forall U, valid st_init U) ->
      Ssafe (@P_init st_init) -> forall U, safe st_init U.
  Proof.
    move=> st all_valid SF U.
    apply: (Ssafe_safe' _ SF).
    - by constructor.
    - by apply: all_valid.
  Qed.

  (* This is too weak... but is a good example*)
  Lemma SsafeN_Ssafe:
    (forall P: Prop, P \/ ~ P) ->
    forall P,
      (forall P, finite (SST_step P)) ->
      (forall n, SsafeN n P) ->
      Ssafe P.
  Proof. by move => EM P A B; apply: (concurrency.konig.konigsafe). Qed.

  (*This is strong enough *)
  Lemma finite_Ssafe_safe':
    (forall P : Prop, P \/ ~ P) ->
    (forall P : ST -> Prop, finite P -> finite (SST_step P)) ->
    forall P, (finite P) ->
         ( forall n : nat, safeN (ST -> Prop) SST_step n P) ->
         Ssafe P.
  Proof. by move => EM FIN P FINP; apply: ( filtered_konigsafe _ finite). Qed.

  Lemma finite_Ssafe_safe:
    (forall P : Prop, P \/ ~ P) ->
    (forall P : ST -> Prop, finite P -> finite (SST_step P)) ->
    forall st, ( forall n : nat, safeN (ST -> Prop) SST_step n (@P_init st)) ->
          Ssafe (@P_init st).
  Proof. move => EM FIN P; apply: finite_Ssafe_safe'=>//. apply: finite_P_init. Qed.
  
  Definition possible_image st st' U:= valid st U /\ exists U', STEP st U st' U'.
  Definition finite_on_x {X Y} (A:X->Y->Prop):= 
    exists n (f: nat -> X), forall x y, A x y -> exists i, (i < n) /\ f i = x.
  Lemma finite_rel_generalize {X Y} (V: X -> Y -> Prop) (R: X -> X -> Y -> Prop):
    forall (propositional_extentionality: True),
      (forall x, finite_on_x (possible_image x)) ->
      forall (P:X -> Prop), finite P ->
                   finite (SStep R V P).
  Proof.
  Admitted.

  Lemma ksafe_safe:
    (forall P: Prop, P \/ ~ P) ->
    forall (propositional_extentionality: True),
    forall (branches_finitely_on_the_state: forall x : ST, finite_on_x (possible_image x)),
    forall st,
      (forall U : SCH, valid st U) ->
      (forall n U, ksafe st U n) ->
      (forall U, safe st U).
  Proof.
    move => EM PROP_EXT FINIT st all_valid SF.
    apply: Ssafe_safe =>//.
    apply: finite_Ssafe_safe=>//.
    by move => st' FINst; apply: (finite_rel_generalize _ _ PROP_EXT).
    by move=> n; apply: ksafe_SsafeN.
  Qed.

   Lemma safe_ksafe':
    forall st,
      (forall U, valid st U -> safe st U) ->
      (forall U, valid st U -> forall n, ksafe st U n).
  Proof.
    move => st SF U VAL n; move: st SF U VAL.
    induction n.
    - constructor.
    - move=> st SF U VAL; specialize (SF _ VAL); inversion SF.
      apply: (sft_step _ _ _ st' U' H)=> U'' VAL'.
      apply: IHn=>//.
  Qed.
  
  Lemma safe_ksafe:
    forall st,
      (forall U : SCH, valid st U) ->
      (forall U, safe st U) ->
      (forall n U, ksafe st U n).
  Proof. move => st all_valid SF n U; apply: safe_ksafe'=>//. Qed.

End Safety.

