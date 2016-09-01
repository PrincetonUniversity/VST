(** *Notice: This file is very sketchy at the moment. Read at your own risk.*)


From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
      
Require Import Coq.ZArith.ZArith.

Require Import compcert.common.Memory.

Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.

Require Import concurrency.konig.

Context (ST:Type)(SCH:Type).
Context (STEP:ST->SCH->ST->SCH-> Prop).
Context (valid: ST-> SCH -> bool).
Axiom valid_dec: forall st U, {valid st U} + {~ valid st U}.


Axiom schedule_independence:
  forall s1 s2 U1 U2, STEP s1 U1 s2 U2 ->
                 U1 = U2 \/ forall U2', exists U1', STEP s1 U1' s2 U2'.
Axiom schedule_dec:
  forall (U U':SCH), {U=U'} + {U<>U'}.

Inductive ksafe (st:ST) U: nat -> Prop :=
|sft0: ksafe st U 0
|sft_step: forall n st' U', STEP st U st' U' -> (forall U'', valid st' U'' -> ksafe st' U'' n) -> ksafe st U (S n).

CoInductive safe st U: Prop:=
  | csft_step: forall st' U', STEP st U st' U' -> (forall U'', valid st' U'' -> safe st' U'') -> safe st U.

Definition SST:= ST -> Prop.
Definition is_in (st:ST)(P:SST):= P st. 
(*Notation enth:= (List.nth_error).*)
Infix "\In":= (is_in) (at level 20, right associativity).

Inductive RRR {X Y: Type} (R: X -> X -> Y -> Prop)(valid:X->Y->Prop) (P P':X -> Prop) : Prop:=
    | blahblah: (forall x y, P x -> valid x y -> exists x', R x x' y /\ P' x') ->
                (forall x', P' x' -> exists x y, R x x' y /\ P x /\ valid x y) ->
                RRR R valid P P'.
Definition R := RRR (fun st st' U => exists U', STEP st U st' U') valid.
(*Inductive R (P P': SST): Prop:=
|blah :
   (forall st U, st  \In P -> valid st U -> exists st' U', STEP st U st' U' /\ st' \In P') ->
   (forall st',  st' \In P' -> exists st U U', STEP st U st' U' /\ st \In P /\ valid st U ) ->
   R P P'.*)

(*Definition R (st st': (ST * (ST -> SCH -> Prop))): Prop:= R' (fst st) (snd st) (fst st') (snd st').*)

Definition my_safeN:= konig.safeN (SST) R. 
Definition my_safe:= konig.safe (SST) R.
Inductive P_init {st_init:ST}: SST:=
  |ItIsMe: P_init st_init. 

Lemma blahh: forall n P,
    my_safeN n P -> forall st U, st \In P -> valid st U -> ksafe st U n.
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
Corollary blahh': forall n st,
    my_safeN n (@P_init st) -> forall U, valid st U -> ksafe st U n.
Proof. move=> n st mysN U VAL. apply: (blahh n P_init mysN) => //. Qed.

Inductive RR' st: ST-> Prop:=
    | steping_step U U' st':
        valid st U -> STEP st U st' U' ->
        RR' st st'.
Axiom finite_steping_step: forall st, finite (RR' st).
Lemma hhalb: forall n P,
    (forall st U, st \In P -> valid st U -> ksafe st U n) ->
    my_safeN n P.
Proof.
  induction n.
  - constructor.
  - move=> P HH.
    pose (P':= fun st' => exists st U U', P st /\
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
Lemma hhalb': forall st_init,
    (forall U, valid st_init U) ->
    forall n, (forall U, ksafe st_init U n) ->
           my_safeN n (@P_init st_init).
Proof.
  move => st_init all_valid n Uksf.
  apply hhalb => st' U' inPinit val.
  inversion inPinit; subst st'.
  apply: Uksf.
Qed.

Lemma coinductive_safety_equivalence: forall P,
    my_safe P -> forall st U, st \In P -> valid st U -> safe st U.
Proof.
  cofix=> P SF st U. 
  inversion SF; subst x; rename x' into P'.
  inversion H => /H1 H1' /H1' [] st' [] [] U' STP inP'.
  apply: (csft_step _ _ st' U')=>// U'' VAL'.
  apply: (coinductive_safety_equivalence P')=> //.
Qed.

Lemma coinductive_safety_equivalence': forall st_init,
    (forall U, valid st_init U) ->
    my_safe (@P_init st_init) -> forall U, safe st_init U.
Proof.
  move=> st all_valid SF U.
  apply: (coinductive_safety_equivalence _ SF).
  - by constructor.
  - by apply: all_valid.
Qed.

Check concurrency.konig.konigsafe.
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
  
Lemma finit_to_infinite_safety_parallel:
  (forall P: Prop, P \/ ~ P) ->
  forall P,
    (forall P, finite (Top.R P)) ->
    (forall n, my_safeN n P) ->
    my_safe P.
Proof. move => EM P A B.
       apply: (concurrency.konig.konigsafe)  => //.
Qed.

Lemma finite_P_init: forall {st}, finite (@P_init st).
Proof.
  move =>st. exists 1, (fun _ => st) => st' HH.
  inversion HH. exists 0; split; auto.
Qed.

Definition possible_image st st' U:= valid st U /\ exists U', STEP st U st' U'.
Definition finite_on_x {X Y} (A:X->Y->Prop):= 
  exists n (f: nat -> X), forall x y, A x y -> exists i, (i < n) /\ f i = x.
Lemma finite_rel_generalize {X Y} (valid: X -> Y -> Prop) (R: X -> X -> Y -> Prop):
  forall (propositional_extentionality: True),
  (forall x, finite_on_x (possible_image x)) ->
  forall (P:X -> Prop), finite P ->
               finite (RRR R valid P).
Proof.
Admitted.

Lemma finit_to_infinite_safety:
  (forall P: Prop, P \/ ~ P) ->
  forall (propositional_extentionality: True),
  forall (branches_finitely_on_the_state: forall x : ST, finite_on_x (possible_image x)),
  forall st,
    (forall U : SCH, valid st U) ->
      (forall n U, ksafe st U n) ->
      (forall U, safe st U).
Proof.
  move => EM PROP_EXT FINIT st all_valid SF.
  apply: coinductive_safety_equivalence' =>//.
  
  eapply ( filtered_konigsafe _ finite)=> //.
  rewrite /R.
  - clear - FINIT PROP_EXT.
    move => st' FINst.
    apply: (finite_rel_generalize _ _ PROP_EXT) =>//. 
    apply: finite_P_init.
  - move=> n; apply: hhalb' => //.
Qed.

Print Assumptions finit_to_infinite_safety.


Definition extract_exist st U n (SF: ksafe st U n.+1): SST.
    Proof.
      inversion SF.
    Inductive PPP (P:SST) n (HH: forall st U, st \In P -> valid st U -> ksafe st U n.+1):=
      | AAA: forall st U (is_in: st \In P) (VAL:valid st U), 
    
    pose (P':= ).
    apply: (safeS _ _ n P).
    
    Lemma passing: forall {A} (a b c:seq A) x, a = b++(x::c) -> a=(b++[::x])++c.
    Proof.
      move => A a b c x sum.
      rewrite -catA cat1s=> //.
    Qed.

    Record state_and_safe n: Type:=
      { which_state: ST; state_is_safe: forall U, valid which_state U -> ksafe which_state U n}.
    Inductive RR st: ST-> Prop:=
    | steping_step U U' st':
        valid st U -> STEP st U st' U' ->
        RR st st'.
    
    Program Fixpoint list_possible_steps' (f:nat->ST) st partial_results i:=
      match i with
      | 0 => partial_results
      | S j => (f i) :: partial_results
      end.
    Definition list_possible_steps (st: ST): seq ST.
    Proof.
      assert (HH:= finite_steping_step st).
      match (finite_steping_step st) with
      | _ => True
      end.
      
      
    Program Definition steps n (st:ST) (P:SST) (i:nat)
            (H1: enth P i = Some st)
            (H2: forall (i : nat) (st : ST) (U : SCH),
                enth P i = Some st -> valid st U -> ksafe st U n.+1):=
      
      
    .
    Program Fixpoint step' n (P head tail:SST) (PROOF: P = head ++ tail) (partial_result: seq (state_and_safe n)):=
      match tail with
      | [::] => partial_result
      | st::tail' => step' n P (head++[::st]) tail' _ (partial_result)
      end.
    Next Obligation.
      rewrite -(passing (head ++ st :: tail')); reflexivity.
    Qed.
    
    Definition step (P:SST):=
      match P with
      | [] => []
      
    pose (P':= match ).

    apply: (safeS ).
    

    Focus 2.
    apply IHn. 
    move => i st U inP VAL.
    
    + constructor.
      move=> i st U inP VAL.
      
    inversion HH; subst.
    inversion H0.
    move: VAL inP => /H H' /H' [] j [] st' [] U' [] STP inx'.
    apply: (sft_step st U n st' U' STP)=> U'' VALID'.
    apply: (IHn x' _ j)=>//.
Qed.



Definition STEP' stU stU':= STEP (fst stU) (snd stU) (fst stU') (snd stU').

Lemma finite_somethign: (forall x, finite (STEP' x)) -> forall P, (finite (fun stU=> P (fst stU) (snd stU)))-> finite (R P).
Proof.
  move => FIN1 P [] n1 [] f1 FIN2. unfold finite.

  
Lemma blahh_init: forall n st,
    (forall U, valid st U) ->
    my_safeN n (@P_init st) -> forall U, ksafe st U n.
Proof.
  move=> n st INIT msf U. clear INIT.
  apply: (blahh n (@P_init st)) => //.
  - move=> st' U1 U2 PstU1 validstU2.
    by inversion PstU1; subst;
    constructor.
Qed.




Inductive ksafe1 st U: nat -> Prop:=
|sft_O1: ksafe1 st U 0
|sft_R1: forall n st' U', R st U st' U' -> ksafe1 st' U' n -> ksafe1 st U (S n).

Inductive ksafe2 st U: nat -> Prop:=
|sft_O2: ksafe2 st U 0
|sft_Req: forall n st', R st U st' U -> ksafe2 st' U n -> ksafe2 st U (S n)
|sft_Rne: forall n st' U', R st U st' U' -> U <> U' -> (forall U'', ksafe2 st' U'' n) -> ksafe2 st U (S n).

Inductive ksafe1_eq st U: ST -> nat -> Prop:=
|sft_O1': ksafe1_eq st U st 0
|sft_R': forall n st' st'', R st U st'' U -> ksafe1_eq st'' U st' n -> ksafe1_eq st U st' (S n).

Inductive ksafe1_ne st U: nat -> Prop:=
|sft_O1'': ksafe1_ne st U 0
|sft_R'': forall n st' U', R st U st' U' -> U <> U' -> ksafe1 st' U' n -> ksafe1_ne st U (S n).

Lemma split_ksafe1: forall n st U,
    ksafe1 st U n ->
    exists i st', i <= n /\ ksafe1_eq st U st' i /\ ksafe1_ne st' U (n - i).
Proof.
  induction n => st U ksf.
  - exists 0, st; split => //; split;
    constructor => //.
  - inversion ksf; subst n0.
    destruct (schedule_dec U U').
    + subst U'.
      move: H1 => /IHn [] i [] st'' [] ineq [] ksf_eq ksf_ne.
      exists (S i), st''; split => //; split.
      * apply: (sft_R' st U i st'' st')=> //.
        replace (n.+1 - i.+1) with (n - i) => // .
      * exists 0, st; split => //. split; econstructor; eauto.
Qed.

Lemma strong_induction: forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
    forall n : nat, P n.
Proof.
  move => P HP n.
  cut (forall k, k < n -> P k).
  move => /HP //.
  induction n => // k / ltP /lt_n_Sm_le /le_lt_eq_dec [/ltP| -> ].
    by apply: IHn.
    apply: HP. apply IHn.
Qed.
        
Theorem safe1_safe2:
  forall n st,
    (forall U, ksafe1 st U n) -> (forall U, ksafe2 st U n). 
Proof.
  apply: strong_induction=> n all st sft1 U.
  move: (sft1 U)=> /split_ksafe1 [] k [] st' [] ineq [] sft1_eq sft1_ne.
  Lemma ksafe1_eq_ksafe2:
    forall n k, k <= n ->
           forall st U st',
             ksafe1_eq st U st' k -> ksafe2 st' U (n - k) -> ksafe2 st U n.
  Proof.
    (*first rewrite the statemente a little*)
    move => n k ineq.
    pose (m:= n - k).
    assert (HH: n = m + k)=> //.
    { symmetry. by apply: subnK. }
    rewrite -/m HH.
    clear HH ineq; move: k m; clear n.

    (*now, onward to the proof*)
    induction k => m st U st' A.
    - inversion A.
      replace (m + 0) with m => //.
    - move=> B. inversion A; subst.
      replace (m + k.+1) with (m + k).+1=>//.
      apply: (sft_Req st U (m + k) st'') => //.
      apply: (IHk _ _ _ st') => //.
  Qed.
  destruct (zerop k).
  - subst k; inversion sft1_eq; clear sft1_eq; subst st'.
    replace (n-0) with n in sft1_ne.
    inversion sft1_ne.
    + constructor.
    + subst n.
      apply: (sft_Rne _ _ _ st' U' H H0).
      apply: all=>// U''.
      move: H => /schedule_independence [nop | stp].
      * contradict nop => //.
      * move: (stp U'') => [] U0 step.
        move: (sft1 U0) => sft1'.
        inversion sft1'.
        (*Wrong!!!*)
        (*when I change the schedule, *)
        specialize (sft1 U). inversion sft1.
  apply: (ksafe1_eq_ksafe2 n k ineq _ _ st')=>//.
  apply: all.
  
  
  

  
  move=> n st sf U.
  induction n.
  - apply: SFT'.
  - 

    
  inversion HH.
  destruct (schedule_dec U U').
  - subst U'.
    move: X H.
    clear - st H.
    move: st st' H.
    cofix HH => st st' stp.
    apply (SFT1 st U st') => //.
    apply: HH.
    generalize dependent st.
  
  cofix IH.
  move: (sf U)=> HH. inversion HH.
  - subst U'; apply: (SFT1 st U st')=> //.
    apply IH => U'.
    move: (sf1 U') => sf1'; inversion sf1'.
    
    


  
  
Module Safety.
  Declare Module SCH: Scheduler. Import SCH.
  Context (G:Type)(tstate:Type).
  Notation event_trace := (seq unit). (*seq machine_event*)
  Definition MachState : Type:= (schedule * event_trace * tstate)%type.
Context
  (MachStep: G -> MachState -> mem -> MachState -> mem -> Prop)
  (halted: MachState -> option Values.val).
Parameter MachStepAxiom: forall ge st m st' m',
    MachStep ge st m st' m' ->
    fst (fst st') = fst (fst st) \/
      fst (fst st') = schedSkip (fst (fst st)).


(** Schedule safety of the coarse-grained machine*)

Context (ge : G).

Notation step:= (MachStep ge).

Inductive step': MachState -> mem -> MachState -> mem -> Prop :=
| Halt: forall ms m, halted ms -> step' ms m ms m
| Cstep: forall ms m ms' m', step ms m ms' m' -> step' ms m ms' m'.

Inductive ksafe (st : MachState) (m : mem) : nat -> Prop :=
| Safe_0: ksafe st m 0
| HaltedSafe: forall n, halted st -> ksafe st m n
| CoreSafe : forall tr tp' m' n 
               (Hstep: step st m (fst (fst st),tr,tp') m')
               (Hsafe: ksafe (fst (fst st),tr,tp') m' n),
    ksafe st m (S n)
| AngelSafe: forall tr tp' m' n
               (Hstep: step st m (schedSkip (fst (fst st)),tr,tp') m')
               (Hsafe: forall U'', ksafe (U'',tr,tp') m' n),
    ksafe st m (S n).

CoInductive safe (st : MachState) (m : mem) : Prop :=
  | CHaltedSafe: halted st -> safe st m
  | CCoreSafe : forall tr tp' m'
                 (Hstep: step st m (fst (fst st),tr,tp') m')
                 (Hsafe: safe (fst (fst st),tr,tp') m'),
      safe st m
  | CAngelSafe: forall tr tp' m'
                 (Hstep: step st m (schedSkip (fst (fst st)),tr,tp') m')
                 (Hsafe: forall U'', safe (U'',tr,tp') m'),
      safe st m.

Definition state:=  (event_trace * tstate * mem)%type.

(* ** Dont know if this is needed... might work... might not *)
(* Non- halting safety  *)
CoInductive safe' (st: MachState) (m: mem) : Prop:=
| CCoreSafe' : forall tr tp' m'
                 (Hstep: step' st m (fst (fst st),tr,tp') m')
                 (Hsafe: safe' (fst (fst st),tr,tp') m'),
    safe' st m
| CAngelSafe': forall tr tp' m'
                 (Hstep: step' st m (schedSkip (fst (fst st)),tr,tp') m')
                 (Hsafe: forall U'', safe' (U'',tr,tp') m'),
    safe' st m.

Lemma safe_safe': forall st m, safe st m <-> safe' st m.
Proof.
  move => [[U trac] st] m; split; move: U trac st m.
  - cofix => U trac st m [] /=.
    + move => halt; cofix.
      apply: CCoreSafe' => /=.
      apply: Halt => //.
      exact safe_safe'0.
    + move => tr tp' m' stp sf.
      
      
      ->; move: (CCoreSafe' (U,nil,st) m st m) => /= H halt.
      apply: H.
      * apply: Halt => //.
      * apply: safe_safe'; apply:CHaltedSafe=>//.
    + move=> tp' m' stp sf. move: (CCoreSafe' (U,trac,st) m tp' m') => /= H.
      apply: H.
      * apply: Cstep => //.
      * apply: safe_safe'=> //.
    + move=> tp' m' stp sf. move: (CAngelSafe' (U, trac, st) m tp' m') => /= H.
      apply: H.
      * apply: Cstep => //.
      * move  => U''; apply: safe_safe'=>//.
  - cofix=> U trac st m [] /= tp' m'. [].
    + constructor 1 => //.
    + intros. *)
      
Inductive preservation P st m: Prop :=
| pres_halt: halted st -> preservation P st m
| pres_cstep: forall tr tp' m' 
               (Hstep: step st m (fst (fst st),tr,tp') m'),
               P (fst (fst st),tr,tp') m' ->
    preservation P st m
| pres_astep:  forall tr tp' m'
                 (Hstep: step st m (schedSkip (fst (fst st)),tr,tp') m'),
               (forall U'', P (U'',tr,tp') m') -> 
    preservation P st m.
          
Definition stable (P : MachState -> mem -> Prop): Prop :=
forall st m, P st m  -> preservation P st m.
Definition kt_safe st m := exists P, P st m /\ stable P.

Lemma kt_safe_safe st m : safe st m <-> kt_safe st m.
Proof.
  split => [H | [P [Pstm stbl]]].
  - exists safe; split; auto; clear.
    move => st m H.
    case H.
    + move => halt. apply: pres_halt=>//.
    + move=> tr tp' m' stp sf; apply: (pres_cstep _ _ _ tr tp' m')=>//.
    + move=> tr tp' m' stp sf; apply: (pres_astep _ _ _ tr tp' m')=>//.
  - move: st m Pstm.
    cofix=> [[[U trac] st] m] Pstm.
    case (stbl _ m Pstm).
    + move => halt. apply: CHaltedSafe => //.
    + move => /= tr tp' m' stp Pstm'.
      apply: (CCoreSafe _ _ tr tp' m') =>//; apply: kt_safe_safe=> //.
    + move => /= tr tp' m' stp Pstm'.
      apply: (CAngelSafe _ _ tr tp' m') =>// U''; apply: kt_safe_safe=> //.
Qed.

Lemma safety_ksafety:
  forall st m,
    safe st m -> forall n, ksafe st m n.
        move => st m Sf n. move: st m Sf.
        induction n.
        - constructor.
        - move => st m Sf.
          inversion Sf.
          + constructor 2 => //.
          + apply: (CoreSafe _ _ tr tp' m' _) => //. apply: IHn => //.
          + apply (AngelSafe _ _ tr tp' m') => // U''.
            apply: IHn => //.
Qed.

Definition finite {X Y} (R:X -> Y -> Prop) := concurrency.konig.finite (fun x => R (fst x) (snd x)).
Definition not_ex_forall: forall {A B} (P : A -> B -> Prop), ~ (exists a b, P a b) <-> (forall a b, ~ P a b).
Proof.
  move => A B P; split => HH.
  - rewrite /not => a b Pab; apply: HH; exists a, b=>//.
  - rewrite /not => [[a [b Pab]]]. apply: (HH a b) => //.
Qed.
Definition not_ex_forall': forall {A B} (P : A -> B -> Prop), (forall a b, ~ P a b) -> ~ (exists a b, P a b).
Proof. intros. eapply not_ex_forall; auto. Qed.

Definition upd {X} f (n:nat) (a:X):= fun x => if Nat.eq_dec x n then a else f x.

Lemma ksafety_safety:
  (forall P, P \/ ~P) ->
  (forall st m, finite (step st m)) ->
  forall st m,
    (forall n, ksafe st m n) -> safe st m.
  Proof.
    move => EM FinBranch st m ks.
    apply kt_safe_safe.
    unfold kt_safe in *.
    move: (EM); rewrite concurrency.konig.EM_ABS => ABS.
    apply: ABS.
    move: (@konig.not_ex_forall (MachState -> mem -> Prop) (fun P: MachState -> mem -> Prop => P st m /\ stable P)) => [] A B /A nex.
    apply (nex (fun st m => forall n, ksafe st m n)).
    split=>//. 
    clear ks st m A B nex => st m ks.
    Inductive R: (MachState * mem) -> (MachState * mem) -> Prop:=
    | Rstep: forall stm stm', step (fst stm) (snd stm) (fst stm') (snd stm') -> R stm stm'
    | Rhalt: forall stm, halted (fst stm) -> R stm stm.
    (*pose (R:= fun stm stm' => step (fst stm) (snd stm) (fst stm') (snd stm')). *)
    pose (safeN:= fun n stm => ksafe (fst stm) (snd stm) n).
    assert (FinBranch': konig.finite (R (st, m))).
    { move: (FinBranch st m) => [] n [] f fb.
      exists (S n), (upd f n (st, m)) => x rel. 
      inversion rel; subst.
      - move: H => /= /fb [] i [A B].
        exists i; split => //. omega.
        rewrite /upd.
        { destruct (Nat.eq_dec i n).
          contradict e; clear - A; omega.
          auto. }
      - exists n. split; [omega|].
        rewrite /upd.
        destruct (Nat.eq_dec n n)=> //; omega.
    }
    pose proof @ramsey_inf _ (R (st, m)) safeN EM FinBranch'.
    assert_specialize H.
    {
      move=> n. exists n; split=> //.
      specialize (ks (S n)).
      inversion ks.
      - exists (st, m); split.
        + apply: Rhalt=>//.
        + apply: HaltedSafe=>//.
      - exists ((fst (fst st), tr, tp'), m'); split => //.
        apply: Rstep=> //.
      - exists ((schedSkip (fst (fst st)), tr, tp'), m'); split => /=.
        + apply: Rstep=> //.
        + apply: (Hsafe ((schedSkip (fst (fst st))))).
    }

    unfold safeN in H.
    move: H => [[[[U' tr'] st'] m'] [ ]] rel; inversion rel=> /=.
    - subst=> /=. rewrite /safeN=> /= inft.
      move: (MachStepAxiom _ _ _ _ _ H) => /= [UU |UU ].
      + move: H; rewrite UU => stp.
        rewrite UU in inft. assert (HH:=pres_cstep (fun st m => infinite (fun n => ksafe st m n)) st m tr' st' m' stp inft).
        unfold infinite in HH.
        inversion HH.
        * eapply pres_halt=> //.
        * eapply pres_cstep=> //; eauto=> n.
          move: (H n)=> [] n' [ineq ksf].
          admit.
        * eapply pres_astep=> //; eauto=> /= U'' n.
          move: (H U'' n)=> [] n' [ineq ksf].
          admit.
      + move: H; rewrite UU => stp.
        rewrite UU in inft. assert (HH:=pres_astep (fun st m => infinite (fun n => ksafe st m n)) st m tr' st' m' stp).
        simpl in HH.
          
    exists x'; split; auto.
    intros n.
    destruct (inf n) as (n' & ln' & sa').
    eapply safeN_le; eauto.
  Qed.
  
            