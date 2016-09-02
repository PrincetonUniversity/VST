(** *Notice: this is a bunch of old ideas. They need to be cleaned up*)
(** *You shouldn't be looking here *)

From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
      
Require Import Coq.ZArith.ZArith.

Require Import compcert.common.Memory.

Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.

Require Import concurrency.konig.


Definition closed (P:ST -> SCH -> Prop):=
  forall st U1 U2, P st U1 -> valid st U2 -> P st U2.

   
Inductive R' (P P': ST -> SCH -> Prop): Prop:=
|blah' :
    (forall st U, P st U -> exists st' U', STEP st U st' U' /\ P' st' U') ->
    (forall st' U', P' st' U' -> exists U st, P st U /\ STEP st U st' U') ->
    closed P' ->
    R' P P'.

(*Inductive R (P P': SST): Prop:=
|blah :
   (forall st U, st  \In P -> valid st U -> exists st' U', STEP st U st' U' /\ st' \In P') ->
   (forall st',  st' \In P' -> exists st U U', STEP st U st' U' /\ st \In P /\ valid st U ) ->
   R P P'.*)


(*Definition R (st st': (ST * (ST -> SCH -> Prop))): Prop:= R' (fst st) (snd st) (fst st') (snd st').*)

Section Safety.
  Axiom valid_dec: forall st U, {valid st U} + {~ valid st U}.

  Axiom schedule_independence:
    forall s1 s2 U1 U2, STEP s1 U1 s2 U2 ->
                   U1 = U2 \/ forall U2', exists U1', STEP s1 U1' s2 U2'.

    Inductive RR' st: ST-> Prop:=
  | steping_step U U' st':
      valid st U -> STEP st U st' U' ->
      RR' st st'.
    Axiom finite_steping_step: forall st, finite (RR' st).


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
    SsafeN n (@P_init st) -> forall U, ksafe st U n.
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
  
            