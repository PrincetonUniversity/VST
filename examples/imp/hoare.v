Require Import Relations.
Require Import msl.msl_standard.

Require Import imp.

(* Gives us a logic over nats *)
Existing Instance ag_nat.

(* Build the logic over worlds.  We take tuples of
   a nat, a local env, and a memory.  The nat exists
   to let us define the |> operator and the Geodel Leob
   rule in the usual way.  We get a SA by the obvious
   combination of SAs on locals and mems with the trival
   SA on nats.
*)
Definition world := (nat * (locals * mem))%type.

Definition world_sa : sepalg world :=
  sa_prod (sa_equiv nat) (sa_prod locals_sa mem_sa).
Existing Instance world_sa.

Definition world_age : ageable world :=
  ag_prod nat (locals * mem) ag_nat.
Existing Instance world_age.

Definition world_asa : ASA world :=
 asa_prod nat (locals * mem) (sa_equiv nat) ag_nat (sa_prod locals_sa mem_sa) asa_nat.
Existing Instance world_asa.

(* Convenience lemmas that pin down the type of a general lemma
   about the product ASA.
*)
Lemma world_nec_split : forall n x n' x',
  @necR world world_age (n,x) (n',x') <-> necR n n' /\ x = x'.
Proof.
  apply prod_nec_split.
Qed.

Lemma world_later_split : forall n x n' x',
  @laterR world world_age (n,x) (n',x') <-> laterR n n' /\ x = x'.
Proof.
  apply prod_later_split.
Qed.

(* Define the safey policy we use to build up the hoare tuple *)
Definition immed_safe (pu:program_unit) (st:state) :=
  fst (fst st) = knil \/
  exists st', step' pu st st'.

Fixpoint stepn (pu:program_unit) (n:nat) (st1 st2:state) {struct n} : Prop :=
  match n with
  | 0 => st1 = st2
  | S n' => exists st', step' pu st1 st' /\ stepn pu n' st' st2
  end.

Local Open Scope pred.

Program Definition safen (pu:program_unit) (k:ctl) : pred world :=
  fun w => forall n', n' <= fst w ->
    forall st', stepn pu n' ((k,fst (snd w)),snd (snd w)) st' -> immed_safe pu st'.
Next Obligation.
  apply H0 with n'; auto.
  hnf in H. destruct a; simpl in *; try discriminate.
  destruct n. inv H. inv H. simpl in *. omega.
  hnf in H. destruct a; simpl in *; try discriminate.
  destruct n. inv H. inv H. simpl in *. auto.
Qed.

(* Lift a predicate on worlds to a pred on nats.  Then
   'lift P' is true when P holds in all locals and memories.
*)
Program Definition lift (P:pred world) : pred nat :=
  fun n => forall rho m, P (n,(rho,m)).
Next Obligation.
  eapply pred_hereditary with (a,(rho,m)); eauto.
  hnf in *. simpl in *. rewrite H. auto.
  apply H0.
Qed.

Obligation Tactic := idtac.

(* Expression evaluation.  Note this is not a tight formula.
   We will almost always use && rather than * to combine eval
   in to a larger formula.
*)
Program Definition eval (e:expr) (v:val) : pred world :=
  fun w => e (fst (snd w)) = Some v.
Next Obligation.
  repeat intro.
  destruct a. destruct n; inv H.
  auto.
Qed.

Definition locpred := locals -> Prop.
Definition mempred := mem -> Prop.

(* Local i has value v *)
Definition hasval (i:ident) (v:val) : locpred :=
  fun rho =>
    LocalsMap.map_val i rho = Some v /\
    LocalsMap.map_share i rho = Share.top /\
    forall i', i <> i' -> LocalsMap.map_val i' rho = None.

Definition anylocals : locpred :=
  fun rho => True.

(* Address a has value v with share sh. *)
Definition mapsto (a:addr) (sh:Share.t) (v:val) : mempred :=
  fun m =>
    MemMap.map_val a m = Some v /\
    MemMap.map_share a m = sh /\
    forall a', a <> a' -> MemMap.map_val a' m  = None.

(* Here we have coercions that turn flat predicates on locals
   or memories into hereditary predicates on worlds.
 *)
Program Definition lift_loc (P:locpred) : pred world :=
  fun x => P (fst (snd x)) /\ identity (snd (snd x)).
Next Obligation.
  repeat intro.
  hnf in H. destruct a; destruct a'.
  simpl in *. destruct n; simpl in *; try discriminate.
  inv H. auto.
Qed.

Program Definition lift_mem (P:mempred) : pred world :=
  fun x => P (snd (snd x)) /\ identity (fst (snd x)).
Next Obligation.
  repeat intro.
  hnf in H. destruct a; destruct a'.
  simpl in *. destruct n; simpl in *; try discriminate.
  inv H. auto.
Qed.

(* "unlifting" operation which requires empty locals and memories *)
Program Definition lift_nat (P:pred nat) : pred world :=
  fun x => P (fst x) /\ identity (fst (snd x)) /\ identity (snd (snd x)).
Next Obligation.
  repeat intro.
  destruct a; destruct a'.
  hnf in H. simpl in H.
  destruct n; simpl in *; try discriminate.
  inv H. intuition.
  apply pred_hereditary with (S n0).
  reflexivity.
  auto.
Qed.

Coercion lift_loc : locpred >-> pred.
Coercion lift_mem : mempred >-> pred.

(* Local i has some unspecified value *)
Definition defined (i:ident) : pred world :=
  EX v:val, hasval i v.

(* P is a precondition for running control k in program p. *)
Definition guards (pu:program_unit) (P:pred world) (k:ctl) : pred nat :=
  lift (P --> safen pu k).

(* R is a precondition for returning into control k.  F is an additional frame.*)
Definition rguards (pu:program_unit) (R:val -> pred world) (F:pred world) (k:ctl) : pred nat :=
  All e:expr, guards pu ((EX v:val, eval e v && R v) * F) (kseq (ret e) k).

(* The continuation-passing hoare tuple of partial correctness.  In short,
   the hoare tuple holds if, whenever the postconditions guard
   some continuation k, it is the case that the precondition guards
   (kseq c k).
 *)
Definition hoare_ (pu:program_unit) (R:val -> pred world) (P:pred world) (c:cmd) (Q:pred world) : pred nat :=
        All k:ctl, All F:pred world,
         (rguards pu R F k &&
          guards pu (Q * F) k) -->
          guards pu (P * F) (kseq c k).


(* We vefify programs by defining function specifications in the usual
   way, by defining pre and postconditions for each function.  We
   use an additional type 'fs_A' to allow information sharing between
   the pre and post.  At call sites, the verifier chooses some appropriate
   element of 'fs_A'.  To allow the pre and post to reasonably hold
   in the contexts of both the caller and the callee, they must not
   judge local variables directly, but rather take direct arguments
   representing the function actual arguments and return value.
 *)
Inductive fun_spec : Type :=
  { fs_A : Type
  ; fs_pre : fs_A -> list val -> pred world
  ; fs_post : fs_A -> val -> pred world
  ; fs_pre_empty_locals :
      forall a vs w, fs_pre a vs w -> identity (fst (snd w))
  ; fs_post_empty_locals :
      forall a v w, fs_post a v w -> identity (fst (snd w))
  }.

(* A program spec defines specifications for some subset of the
   function identifiers.
*)
Definition prog_spec := ident -> option fun_spec.

(* Given a function declaration and a list of actual arguments, this
   function constructs a formula in SL which describes the initial
   local variable environment of a function.
*)
Definition func_start_locals (fd:fun_decl) (vs:list val) : pred world :=
  let xs := combine (fnd_formals fd) vs ++ (fnd_locals fd) in
    fold_right (fun iv P => hasval (fst iv) (snd iv) * P) emp xs.

(* The precondition for verifying function bodies.  It combines the
   function specification precondition with the local variables
   avaliable at the start of the function. *)
Definition func_pre (fd:fun_decl) (fs:fun_spec) (a:fs_A fs) : pred world :=
  EX vs:list val, fs_pre fs a vs * func_start_locals fd vs.

(* The return postcondition for verifying function bodies.  *)
Definition func_post (fs:fun_spec) (a:fs_A fs) : val -> pred world :=
  fun v => fs_post fs a v * anylocals.

(* We say a function 'i' satisfies a function spec in a program 'pu' provided
   the function has some declaration and that declaration (approximately) satifies
   a hoare tuple describing the expected behavior of the function body. *)
Definition satisfies_fun_spec (pu:program_unit) (i:ident) (fs:fun_spec) : pred nat :=
  EX fd:fun_decl, !!(pu i = Some fd) &&
    All a:(fs_A fs), |>hoare_ pu (func_post fs a) (func_pre fd fs a) (fnd_cmd fd) FF.

(* A program satisfies a program spec if each claimed function spec is satisfied. *)
Definition satisfies_spec (pu:program_unit) (ps:prog_spec) : pred nat :=
    All i:ident, All fs:fun_spec, !!(ps i = Some fs) --> satisfies_fun_spec pu i fs.

(* The validate predicate represents a state of partial verification.
   We have assumed that ps holds for call sites, and we have proved
   under these assumptions that ps' holds.  Typically ps' is a subset
   of ps.  Validation is completed if ps = ps'.
*)
Definition validate (ps:prog_spec) (pu:program_unit) (ps':prog_spec) :=
  |>satisfies_spec pu ps |-- satisfies_spec pu ps'.


(* Some facts about evaluation.  Most importantly, Evaluation passes into larger worlds.
*)

Lemma eval_up : forall e v P Q R,
  (P && R && eval e v) * Q |--
  ((P && R) * Q) && eval e v.
Proof.
  repeat intro.
  destruct H as [wp [wq [? [? ?]]]].
  destruct H0. destruct H0.
  split.
  exists wp; exists wq.
  intuition. split; auto.
  destruct e. simpl in *.
  eapply e with (fst (snd wp)).
  exists (fst (snd wq)).
  destruct H. destruct H4; auto.
  auto.
Qed.

Lemma eval_up' : forall e v P Q,
  (P && eval e v) * Q |--
  (P * Q) && eval e v.
Proof.
  intros.
  rewrite <- (TT_and (eval e v)) at 1.
  rewrite <- (TT_and P) at 2.
  rewrite (andp_com TT P).
  rewrite <- andp_assoc.
  apply eval_up.
Qed.

(* Simultaneous evaluation of a list of expressions *)
Fixpoint list_eval (es:list expr) (vs:list val) : pred world :=
  match es, vs with
  | e::es', v::vs' => eval e v && list_eval es' vs'
  | nil, nil => TT
  | _, _ => FF
  end.

(* List evaluation likewise passes into larger worlds. *)
Lemma list_eval_up : forall es vals P Q,
  (P && list_eval es vals) * Q |--
  (P * Q) && list_eval es vals.
Proof.
  induction es; repeat intro.
  simpl list_eval in *.
  destruct vals.
  rewrite andp_com.
  rewrite TT_and.
  rewrite andp_com in H.
  rewrite TT_and in H.
  auto.
  rewrite andp_com in H.
  rewrite FF_and in H.
  rewrite FF_sepcon in H. elim H.
  simpl list_eval in *.
  destruct vals.
  rewrite andp_com in H.
  rewrite FF_and in H.
  rewrite FF_sepcon in H. elim H.
  rewrite <- andp_assoc in H.
  apply IHes in H.
  destruct H.
  apply eval_up' in H.
  destruct H.
  split; auto.
  split; auto.
Qed.

(* The make_locals function actually satisfies the func_start_locals predicate. *)
Lemma make_locals_func_start_locals : forall fd vs n m,
  identity m ->
  func_start_locals fd vs (n,(make_locals vs fd,m)).
Proof.
  intros. unfold func_start_locals.
  unfold make_locals.
  cut (NoDup (map (@fst _ _) (combine (fnd_formals fd) vs ++ fnd_locals fd))).
  generalize (combine (fnd_formals fd) vs ++ fnd_locals fd).
  intro l. clear fd vs.
  revert n m H. induction l; simpl fold_right; intros.
  unfold LocalsMap.build_map. simpl.
  rewrite identity_unit_equiv.
  split. simpl. split; auto.
  simpl snd. split.
  simpl fst.
  intro. simpl. constructor.
  simpl snd. rewrite identity_unit_equiv in H.
  auto.
  exists (n,(LocalsMap.build_map (a::nil),m)).
  exists (n,(LocalsMap.build_map l,m)).
  intuition.
  split. simpl. split; auto.
  unfold snd.
  split.
  change (a::l) with (a::nil ++ l).
  apply (LocalsMap.build_map_join (a::nil) l).
  simpl. auto.
  simpl snd. rewrite identity_unit_equiv in H. auto.
  simpl. split; auto.
  unfold LocalsMap.build_map.
  unfold hasval. split.
  simpl fold_right.
  unfold LocalsMap.map_val.
  simpl. unfold LocalsMapInput.dec_eq_A.
  destruct a. simpl.
  destruct (eq_nat_dec i i).
  auto.
  elim n0; auto.
  split.
  unfold LocalsMap.map_share. simpl.
  destruct a; simpl.
  unfold LocalsMapInput.dec_eq_A.
  destruct (eq_nat_dec i i). auto.
  elim n0; auto.
  intros.
  unfold LocalsMap.map_val. simpl.
  unfold LocalsMapInput.dec_eq_A.
  destruct a; simpl.
  destruct (eq_nat_dec i i').
  contradiction.
  auto.
  apply IHl. auto. inv H0. auto.

  generalize (fnd_valid fd).
  revert vs.
  generalize (fnd_formals fd).
  induction l; simpl; intros; auto.
  destruct vs. simpl.
  inv H0. clear -H4.
  induction l. auto.
  apply IHl. inv H4; auto.
  simpl.
  inv  H0. constructor; auto.
  intro. apply H3.
  clear -H0.
  revert vs H0.
  induction l; simpl; intros; auto.
  destruct vs. simpl in H0.
  right. apply in_or_app. auto.
  simpl in H0.
  intuition.
  right; eapply IHl; eauto.
Qed.

(* The 'defined' predicate is sufficent to successfully
   perform a local variable update.
 *)
Lemma defined_update : forall i P n rho m v,
  (defined i * P)%pred (n,(rho,m)) ->
  exists rho',
    LocalsMap.map_upd i v rho = Some rho' /\
    (hasval i v * P)%pred (n,(rho',m)).
Proof.
  intros.
  destruct H as [w1 [w2 [? [? ?]]]].
  destruct H0 as [v' ?].
  destruct H0.
  destruct H0 as [? [? ?]].
  apply (LocalsMap.map_upd_success i v) in H3.
  destruct H3 as [r ?].
  generalize H3; intro.
  apply (LocalsMap.map_upd_join _ (fst (snd w2)) rho) in H3.
  destruct H3 as [rho' [? ?]].
  exists rho'. split; auto.
  exists (n,(r,snd (snd w1))).
  exists (n,snd w2).
  split.
  split. simpl. split; auto.
  simpl snd. split.
  simpl fst. auto.
  simpl snd. destruct H. destruct H7; auto.
  split.
  split. simpl. hnf. split; auto.
  eapply LocalsMap.map_gss_val; eauto.
  split.
  eapply LocalsMap.map_set_share2; eauto.
  intros.
  case_eq (LocalsMap.map_val i' r); auto; intros.
  elimtype False.
  erewrite <- LocalsMap.map_gso_val in H8.
  3: eauto.
  rewrite H4 in H8; auto. discriminate.
  auto.
  simpl. auto.
  destruct H. destruct H. simpl in H8. subst n.
  destruct w2; auto.
  destruct H. destruct H6; auto.
Qed.

(* mapsto imp the ability to read from memory *)
Lemma mapsto_val : forall a sh v P n rho m,
  (mapsto a sh v * P )%pred(n,(rho,m)) ->
  MemMap.map_val a m = Some v.
Proof.
  intros.
  destruct H as [w1 [w2 [? [? ?]]]].
  destruct H0. destruct H0 as [? [? ?]].
  destruct H. destruct H5.
  spec H6 a.
  simpl in H6.
  unfold MemMap.map_val in H0.
  unfold lookup_fpm in H0.
  destruct w1 as [? [? ?]].
  simpl in *.
  spec H5 a.
  unfold MemMap.map_share in *.
  unfold lookup_fpm in  H3.
  destruct (proj1_sig m0 a); disc.
  destruct p. inv H0.
  simpl in H6.
  destruct w2; destruct p. simpl in *.
  destruct H; subst.
  unfold  MemMap.map_val.
  unfold lookup_fpm.
  destruct (proj1_sig m1 a).
  destruct (proj1_sig m a).
  2: inv H6.
  destruct p; destruct p0. inv H6. inv H7.
  destruct H0. simpl in *; subst; auto.
  inv H6.
  auto.
Qed.

(* mapsto with the full share imp that
   memory stores will succeed.
 *)
Lemma mapsto_update : forall a v v' P n rho m,
  (mapsto a Share.top v * P)%pred (n,(rho,m)) ->
  exists m',
    MemMap.map_upd a v' m = Some m' /\
    (mapsto a Share.top v' * P)%pred (n,(rho,m')).
Proof.
  intros.
  destruct H as [w1 [w2 [? [? ?]]]].
  destruct H0. destruct H0 as [? [? ?]].
  apply (MemMap.map_upd_success a v') in H3.
  destruct H3 as [m' ?].
  generalize H3; intro.
  apply (MemMap.map_upd_join _ (snd (snd w2)) m) in H5.
  destruct H5 as [m'' [? ?]].
  exists m''; split; auto.
  exists (n,(fst (snd w1),m')).
  exists (n,snd w2).
  split.
  split. split; auto.
  split. simpl fst. destruct H. destruct H7. auto.
  simpl snd. auto.
  split. split; auto.
  simpl. split.
  eapply MemMap.map_gss_val; eauto.
  split.
  eapply MemMap.map_set_share2; eauto.
  intros.
  case_eq (MemMap.map_val a' (snd (snd w1))); auto; intros.
  rewrite H4 in H8; auto. discriminate.
  erewrite MemMap.map_gso_val in H8.
  3: eauto. auto. auto.
  destruct w2. destruct H. destruct H.
  simpl in H. subst n0. simpl in H8. subst n.
  simpl. auto.
  destruct H. destruct H6; auto.
Qed.

(* rguards is insensitive to 'kseq' constructors
   on the top of the stack.
 *)
Lemma rguards_unwind : forall pu R F k1 k2 w1 w2,
  unwind_return k1 = unwind_return k2 ->
  necR w1 w2 ->
  rguards pu R F k1 w1 -> rguards pu R F k2 w2.
Proof.
  do 16 intro.
  spec H1 b.
  spec H1 rho m. spec H1 a'.
  spec H1.
  apply rt_trans with (w2,(rho,m)); auto.
  change (necR (w1,(rho,m)) (w2,(rho,m))).
  rewrite world_nec_split. split; auto.
  spec H1; auto.
  repeat intro.
  destruct n'. simpl in H5. subst.
  spec H1 0. spec H1; auto.
  spec H1 (kseq (ret b) k1,fst (snd a'),snd (snd a')).
  spec H1. simpl. auto.
  inv H1. simpl in H5. discriminate.
  destruct H5. inv H1. inv H10.
  constructor 2. econstructor.
  do 2 econstructor; eauto.
  rewrite <- H. eauto.
  spec H1 (S n') H4 st'.
  apply H1.
  clear - H H5.
  simpl in *.
  destruct H5. destruct H0.
  exists x. split; auto.
  inv H0. inv H7.
  econstructor. econstructor; eauto.
  rewrite H. auto.
Qed.

(* Some additional facts about evaluation *)
Lemma list_eval_join_sub : forall es vs w1 w2,
  join_sub w1 w2 ->
  list_eval es vs w1 ->
  list_eval es vs w2.
Proof.
  induction es; simpl; intros.
  destruct vs. hnf; auto.
  elim H0.
  destruct vs. elim H0.
  destruct H0; split; eauto.
  simpl in H0. simpl.
  destruct a; simpl in H0; simpl.
  eapply e; eauto.
  destruct H. destruct H. destruct H2.
  eauto.
Qed.

Lemma list_eval_evaluate_exprs : forall es vs w,
  list_eval es vs w ->
  evaluate_exprs (fst (snd w)) es vs.
Proof.
  induction es; simpl; intros.
  destruct vs. auto.
  elim H.
  destruct vs. elim H.
  destruct H.
  split; auto.
Qed.


(** Proofs about validation. **)

(* When ps = ps', validation is finished.  Then we know that the program
   actually satisfies the claimed specification.
 *)
Lemma validate_finished : forall ps pu,
  validate ps pu ps ->
  forall n, satisfies_spec pu ps n.
Proof.
  intros.
  assert (TT |-- satisfies_spec pu ps).
  apply goedel_loeb.
  rewrite TT_and. apply H.
  apply H0; auto.
Qed.

(* Validation base case. No claims are proved.*)
Lemma validate_empty : forall pu ps,
  validate pu ps (fun _ => None).
Proof.
  repeat intro. discriminate.
Qed.

(* Validation, interesting case.  We wish to add the proof
   of a new function to the proved set.  To do so, we must
   produce the appropriate hoare tuple which demonstrates the
   correctness of the function body.
*)
Lemma validate_add : forall pu ps' ps i fs fd,
  pu i = Some fd ->

  satisfies_spec pu ps' |--
    All a:(fs_A fs), hoare_ pu (func_post fs a) (func_pre fd fs a) (fnd_cmd fd) FF ->

  validate ps' pu ps ->

  validate ps' pu (fun i' => if eq_nat_dec i i' then Some fs else ps i').
Proof.
  repeat intro.
  hnf in H4.
  destruct (eq_nat_dec i b). subst b.
  inv H4.
  exists fd. split; auto.
  cut ((|>satisfies_spec pu ps') a').
  rewrite <- box_all.
  apply box_positive; auto.
  eapply pred_nec_hereditary; eauto.

  spec H1 a H2.
  spec H1 b b0 a.
  spec H1; auto. spec H1; auto.
  apply pred_nec_hereditary with a; auto.
Qed.

(* Top-level safety theorem.  If we have verified an entire program then
   we can call any of the functions in the program in a state satisfing
   the function's precondition.
 *)
Lemma validate_correct : forall pu ps n i f fs rho m args vals a,
  satisfies_spec pu ps n ->
  ps f = Some fs ->
  evaluate_exprs rho args vals ->
  (fs_pre fs a vals * TT)%pred (n,(rho,m)) ->
  LocalsMap.map_share i rho = Share.top ->
  safen pu (kseq (call i f args) knil) (n,(rho,m)).
Proof.
  intros.
  spec H f fs n. do 2 (spec H; auto).
  destruct H as [fd [? ?]]. simpl in H.
  spec H4 a.
  repeat intro.
  simpl in H5.
  destruct n'; simpl in H6.
  subst st'.
  constructor 2. econstructor.
  econstructor. econstructor; eauto.
  destruct H6 as [st'' [? ?]].
  spec H4 n'. spec H4. simpl.
  rewrite later_nat. omega.
  spec H4 (kcall i rho knil) TT.
  spec H4 n'. spec H4; auto.
  spec H4. split.
  intros e rho' m' w ? ?.
  rewrite exp_sepcon1 in H9.
  destruct H9 as [v ?].
  rewrite andp_com in H9.
  apply eval_up' in H9.
  destruct H9.
  destruct (LocalsMap.map_upd_success i v rho); auto.

  repeat intro.
  destruct n'0; simpl in H13.
  subst st'0.

  constructor 2. econstructor.
  econstructor. econstructor; eauto.
  apply H10.
  simpl. reflexivity.

  destruct H13 as [st''' [? ?]].
  inv H13. inv H20.
  destruct n'0. simpl in H14.
  subst st'0.
  simpl in H16. inv H16.
  constructor 1. auto.
  simpl in H14. destruct H14 as [? [? ?]].
  simpl in H16. inv H16.
  inv H13.
  repeat intro.
  rewrite FF_sepcon in H9. elim H9.

  spec H4 (make_locals vals fd) m (n',(make_locals vals fd,m)).
  spec H4; auto.
  spec H4; auto.
  destruct H2 as [w1 [w2 [? [? ?]]]].
  exists (n',(make_locals vals fd,snd (snd w1))).
  exists (n',(proj1_sig (join_ex_units (make_locals vals fd)),snd (snd w2))).
  split. split. simpl. split; auto.
  simpl snd. split.
  simpl fst. destruct (join_ex_units (make_locals vals fd)); auto.
  simpl snd. destruct H2. destruct H10; auto.
  split. 2: hnf; auto.
  unfold func_pre.
  exists vals.
  exists (n',snd w1).
  exists (n',(make_locals vals fd,proj1_sig (join_ex_units (snd (snd w1))))).
  split. split. simpl. split; auto.
  simpl snd. split.
  simpl fst.
  apply fs_pre_empty_locals in H8.
  destruct w1 as [? [? ?]]. simpl fst.
  rewrite (LocalsMap.map_identity_is_empty l).
  apply LocalsMap.empty_map_join; auto.
  simpl in H8. auto.
  simpl snd.
  match goal with [|- join _ (proj1_sig ?X) _ ] =>
    destruct X; auto
  end.
  split.
  apply pred_nec_hereditary with w1; auto.
  destruct w1.
  rewrite world_nec_split.
  split; auto.
  replace n0 with n.
  rewrite nec_nat. omega.
  inv H2. inv H10.
  simpl in *. congruence.
  apply make_locals_func_start_locals.
  destruct (join_ex_units (snd (snd w1))).
  simpl.
  eapply unit_identity; eauto.

  inv H6.
  inv H13.
  rewrite H in H18. inv H18.
  assert (vals = vals0).
  eapply evaluate_exprs_fun; eauto.
  subst vals0.
  eapply H4; eauto.

  rewrite H in H17. discriminate.
Qed.


(** Now we prove the hoare rules. **)

(* exps in the precondition are equivalant to
   allps bound outside the hoare tuple.
 *)
Lemma hoare_ex : forall ps R A (P:A->pred world) c Q,
  hoare_ ps R (exp P) c Q =
  (All x:A, hoare_ ps R (P x) c Q).
Proof.
  intros. apply equiv_eq.
  do 13 intro.
  spec H b0.
  eapply H; eauto.
  rewrite exp_sepcon1.
  exists b. auto.

  do 12 intro.
  rewrite exp_sepcon1 in H3.
  destruct H3 as [x ?].
  eapply H; eauto.
Qed.


Lemma hoare_fact1 : forall ps X R P c Q,
  X --> hoare_ ps R P c Q |-- hoare_ ps R (lift_nat X * P) c Q.
Proof.
  intros. intros x H.
  intros k F x' H1 H2 rho m x'' H3 H4.
  rewrite sepcon_assoc in H4.
  destruct H4 as [w1 [w2 [? [? ?]]]].
  spec H (fst x''). spec H.
  destruct x''.
  rewrite world_nec_split in H3.
  simpl.
  destruct H3.
  apply rt_trans with x'; auto.

  spec H.
  destruct H4.
  replace (fst x'') with (fst w1); auto.
  destruct H0. destruct H0.
  etransitivity.  apply H0.  auto.

  spec H k F (fst x''). spec H; auto.
  spec H. apply pred_nec_hereditary with x'; auto.
  destruct x''.
  rewrite world_nec_split in H3.
  simpl.
  destruct H3.
  apply rt_trans with x'; auto.

  spec H (fst (snd x'')) (snd (snd x'')).
  spec  H x''. spec H.
  destruct x'' as [? [? ?]]; auto.
  apply H.
  replace x'' with w2; auto.
  assert (identity w1).
  destruct H4.
  rewrite identity_unit_equiv.
  split.
  split; auto.
  destruct H6.
  destruct w1. destruct p.
  split.
  rewrite identity_unit_equiv in H6; auto.
  rewrite identity_unit_equiv in H7; auto.
  apply H6 in H0. auto.
Qed.

Lemma hoare_fact2 : forall ps X R P c Q,
  hoare_ ps R (lift_nat X * P) c Q |-- X --> hoare_ ps R P c Q.
Proof.
  intros. rewrite <- imp_andp_adjoint.
  intros x H.
  destruct H.
  intros k F x' H1 H2 rho m x'' H3 H4.
  spec H k F x' H1 H2 rho m x'' H3.
  spec H.
  rewrite sepcon_assoc.
  exists (proj1_sig (join_ex_units x'')). exists x''.
  intuition.
  destruct (join_ex_units x''); auto.
  destruct (join_ex_units x''); simpl.
  intuition.
  replace (fst x0) with (fst x'').
  apply pred_nec_hereditary with x; auto.
  destruct x''.
  rewrite world_nec_split in H3.
  destruct H3.
  simpl.
  eapply rt_trans; eauto.
  destruct u. destruct H5; auto.
  destruct u. destruct H6.
  eapply unit_identity; eauto.
  destruct u. destruct H6.
  eapply unit_identity; eauto.
  auto.
Qed.

(* Lifted facts in the precondition can be pulled outside,
   or outside facts can be pushed inside. *)
Lemma hoare_fact : forall ps X R P c Q,
  hoare_ ps R (lift_nat X * P) c Q = X --> hoare_ ps R P c Q.
Proof.
  intros. apply equiv_eq. apply hoare_fact2. apply hoare_fact1.
Qed.

(* Lemma for proving the correctness of straight-line instructions.
   The sufficent condition is :
     If the state before satisfies the precondition then there exists
     a post state satisfiing the postcondition.
*)
Lemma hoare_straight : forall pu R c P Q n,
  (forall k rho m F n', n' <= n ->
    proj1_sig (P * F) (n',(rho,m)) ->
    exists rho', exists m',
      step pu k rho m c k rho' m' /\
      proj1_sig (Q * F) (n',(rho',m'))) ->
  hoare_ pu R P c Q n.
Proof.
  intros.
  intros k F a2 ? [? ?] rho m a3 ? ?.
  assert (Ha3: a3 = (fst a3,(rho,m))).
  destruct a3.
  rewrite world_nec_split in H3.
  simpl. f_equal.
  destruct H3; auto.
  destruct (H  k rho m F (fst a3)) as [rho' [m' [? ?]]].
  rewrite <- nec_nat.
  destruct a3.
  rewrite world_nec_split in H3. destruct H3.
  apply rt_trans with a2; auto.
  rewrite <- Ha3. auto.
  spec H2 rho' m' (fst a3,(rho',m')).
  spec H2.
  rewrite world_nec_split. split; auto.
  destruct a3.
  rewrite world_nec_split in H3; destruct H3; auto.
  spec H2. auto.
  repeat intro.
  destruct n'. simpl in H8.
  subst st'.
  constructor 2.
  econstructor.
  rewrite Ha3; simpl.
  econstructor.
  eauto.
  simpl in H8.
  destruct H8 as [st'' [? ?]].
  inversion H8. subst c0 k0 rho0 m0 st''.
  assert ((k',rho'0,m'0) = (k,rho',m')).
  eapply step_fun; eauto.
  rewrite Ha3; simpl. auto.
  inversion H10. subst k' rho'0 m'0.
  apply H2 with n'. simpl. omega.
  auto.
Qed.

(** Now the main hoare rules **)

Lemma hoare_frame : forall pu R c P Q F n,
  hoare_ pu R P c Q n ->
  hoare_ pu (fun v => R v * F) (P * F) c (Q * F) n.
Proof.
  intros. do 10 intro.
  destruct H1.
  repeat rewrite sepcon_assoc in H3.
  destruct H3 as [wP [wF [? [? ?]]]].
  spec H b (F * b0).
  spec H a' H0.
  spec H. split.
  unfold rguards in H1. unfold rguards.
  intro e. spec H1 e.
  repeat intro.
  eapply H1; eauto.
  rewrite exp_sepcon1 in H8.
  rewrite exp_sepcon1.
  destruct H8 as [v ?]. exists v.
  rewrite andp_com in H8.
  rewrite <- sepcon_assoc in H8.
  revert H8.
  apply split_sepcon.
  repeat intro.
  apply eval_up' in H8.
  destruct H8. split; auto.
  hnf; auto.
  repeat rewrite <- sepcon_assoc. auto.

  spec H rho m a'0. spec H; auto.
  spec H; auto.
  exists wP. exists wF.
  intuition.
Qed.


Lemma hoare_skip : forall ps R Q n,
  hoare_ ps R Q skip Q n.
Proof.
  intros. do 2 intro. apply hoare_straight.
  intros. exists rho; exists m.
  split. constructor. auto.
Qed.

Lemma hoare_ret : forall ps R e Q n,
  hoare_ ps R
     (EX v:val, eval e v && R v)
     (ret e)
     Q n.
Proof.
  intros. do 5 intro.
  destruct H0.
  intros rho m w ? ?.
  rewrite exp_sepcon1 in H3.
  destruct H3 as [v ?].
  unfold rguards in H0.
  spec H0 e.
  spec H0 rho m.
  eapply H0; auto.
  rewrite exp_sepcon1. exists v. auto.
Qed.


Lemma hoare_call : forall ps R i f es fs Q n,
  hoare_ ps R
     (lift_nat (satisfies_fun_spec ps f fs) *
     (EX vals:list val, list_eval es vals &&
       EX a:fs_A fs,
         fs_pre fs a vals *
         defined i *
         All v:val,
           fs_post fs a v * hasval i v -* Q))
     (call i f es)
     Q n.
Proof.
  intros.
  intros k F w1 Hw1 [Hrg Hg].
  intros rho m w2 Hw2 H.
  destruct H as [wpre0 [wF [Hj [Hpre HF]]]].
  destruct Hpre as [wsat [wpre [Hjsat [Hsat Hpre]]]].
  destruct Hpre as [args [Hargs [a Hpre]]].
  assert (wpre = wpre0).
  assert (identity wsat).
  rewrite identity_unit_equiv.
  destruct Hsat.
  destruct H0.
  split. split; auto.
  rewrite identity_unit_equiv in H0.
  rewrite identity_unit_equiv in H1.
  split; auto.
  apply H in Hjsat.
  auto.
  subst wpre0.
  rewrite sepcon_assoc in Hpre.
  destruct Hpre as [wpre' [wQ0 [Hj2 [Hpre HQ]]]].
  destruct Hsat as [Hsat Hsat'].
  destruct Hsat as [fd [Hfd Hsat]].
  spec Hsat a. simpl in Hfd.
  repeat intro.

  destruct n'; simpl in H0.
  subst st'.
  constructor 2. econstructor.
  econstructor. econstructor; eauto.
  instantiate (1:=args).
  cut (list_eval es args w2).
  apply list_eval_evaluate_exprs.
  apply list_eval_join_sub with wpre; eauto.

  destruct H0 as [st'' [? ?]].
  inv H0. inv H7.
  rewrite Hfd in H12. inv H12. rename fd0 into fd.
  spec Hsat n'. spec Hsat. simpl.
  apply Rft_Rt_trans with (fst w2).
  replace (fst wsat) with (fst wpre).
  replace (fst wpre) with (fst w2).
  auto.
  destruct Hj.
  destruct H0.
  etransitivity.  symmetry; eassumption. auto.
  destruct Hjsat.
  destruct H0; auto.
  change (laterR (fst w2) n').
  rewrite later_nat. omega.

  revert H1.
  destruct (join_assoc Hj2 Hj) as [w [? ?]].
  spec Hsat (kcall i (fst (snd w2)) k) (lift_mem (eq (snd (snd w)))).
  spec Hsat n'. spec Hsat; auto.
  spec Hsat.
  split.
  intros e rho' m' q Hq ?.
  rewrite exp_sepcon1 in H2.
  destruct H2 as [v' ?].
  generalize HQ; intro HQ'.
  destruct wQ0 as [wQn [wQrho wQm]].
  apply defined_update with _ _ _ _ _ v' in HQ'.
  destruct HQ' as [rho'' [? ?]].
  generalize H3; intro H3'.
  assert (join_sub wQrho (fst (snd w2))).
    apply join_sub_trans with (fst (snd w)).
    destruct H0. destruct H5. eauto.
    destruct H1. destruct H5. eauto.
  destruct H5.
  apply LocalsMap.map_upd_join with _ x (fst (snd w2)) _ _ _ in H3; auto.
  destruct H3 as [rho''' [? ?]].

  repeat intro.
  destruct n'0; simpl in H8.
  subst st'0.
  constructor 2. econstructor.
  econstructor. econstructor; simpl; eauto.
  rewrite andp_com in H2.
  apply eval_up' in H2. destruct H2; auto.
  destruct H8 as [st'' [? ?]].
  inv H8. inv H16.
  simpl in H12. inv H12.
  revert H9.
  assert (v = v').
    rewrite andp_com in H2.
    apply eval_up' in H2.
    destruct H2.
    hnf in H8.
    destruct e.
    simpl in H8, H10.
    congruence.
  subst v'.
  rewrite H17 in H3.
  inv H3.

  spec Hg rho''' (snd (snd q)).
  spec Hg (n'0,(rho''',snd (snd q))).
  spec Hg.
    rewrite world_nec_split; split; auto.
    apply rt_trans with (fst q).
    destruct q.
    rewrite world_nec_split in Hq. destruct Hq.
    apply rt_trans with n'; auto.
    apply rt_trans with (fst w2).
    destruct w2.
    rewrite world_nec_split in Hw2. destruct Hw2.
    auto.
    apply Rt_Rft.
    change (laterR (fst w2) n').
    rewrite later_nat. auto.
    apply Rt_Rft.
    change (laterR (fst q) n'0).
    rewrite later_nat. auto.
  spec Hg.
  assert ((fs_post fs a v -* Q)%pred (n'0,(rho'',wQm))).
    apply pred_nec_hereditary with (wQn,(rho'',wQm)).
    rewrite world_nec_split; split; auto.
    apply rt_trans with (fst q).
    replace wQn with (fst w).
    replace (fst w) with (fst w2).
    apply rt_trans with n'.
    apply Rt_Rft.
    change (laterR (fst w2) n').
    rewrite later_nat; auto.
    destruct q. rewrite world_nec_split in Hq; destruct Hq; auto.
    destruct H1.
    destruct H1; auto.
    destruct H0. destruct H0; simpl in *.
    etransitivity; symmetry; eassumption.
    apply Rt_Rft. change (laterR (fst q) n'0).
    rewrite later_nat; auto.

    revert H4.
    generalize (wQn,(rho'',wQm)).
    clear.
    change (hasval i0 v * (All v0:val, fs_post fs a v0 * hasval i0 v0 -* Q) |-- fs_post fs a v -* Q).
    rewrite <- wand_sepcon_adjoint.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    apply derives_cut
      with (fs_post fs a v * hasval i0 v *
        (fs_post fs a v * hasval i0 v -* Q)).
    apply split_sepcon. hnf; auto.
    do 2 intro.
    spec H v. auto.
    rewrite sepcon_comm.
    rewrite wand_sepcon_adjoint. hnf; auto.

  rewrite andp_com in H2. apply eval_up' in H2.
  destruct H2.
  unfold func_post in H2.
  rewrite sepcon_comm in H2.
  rewrite <- sepcon_assoc in H2.
  destruct H2 as [q1 [q2 [? [? ?]]]].
  destruct H9 as [q3 [q4 [? [? ?]]]].
  destruct H13.

  assert
    (((fs_post fs a v -* Q) * (fs_post fs a v * F))%pred (n'0,(rho''',snd (snd q)))).
    destruct H2. destruct H16.
    destruct H12.
    apply join_com in H18.
    apply H19 in H18.
    destruct H9. destruct H20.
    rewrite H18 in H21.
    unfold mem, locals, LocalsMap.map, MemMap.map in *.
    rewrite <- H13 in H21.
    destruct H0.
    destruct H22.
    simpl snd in H23.
    destruct (join_assoc H23 H21) as [z [? ?]].
    exists (n'0,(rho'',wQm)).
    exists (n'0,(x,z)).
    intuition.
    split. simpl; split; auto.
    simpl snd. split.
    simpl fst. auto.
    simpl snd. auto.
    exists (n'0,(proj1_sig (join_ex_units x),snd (snd q4))).
    exists (n'0,(x,snd (snd wF))).
    intuition.
    split. simpl. split; auto.
    simpl snd. split.
    simpl fst. destruct (join_ex_units x). auto.
    simpl snd. apply join_com; auto.
    assert (fs_post fs a v (n'0,snd q4)).
    apply pred_nec_hereditary with q4; auto.
    destruct q4. rewrite world_nec_split; split; auto.
    replace n0 with (fst q1).
    replace (fst q1) with (fst q).
    apply Rt_Rft. change (laterR (fst q) n'0).
    rewrite later_nat; auto.
    destruct H2. destruct q1; destruct q2; destruct q; simpl in *; congruence.
    destruct H9; auto.

    replace (proj1_sig (join_ex_units x),snd (snd q4))
      with (snd q4); auto.
    destruct q4; simpl. destruct p. simpl. f_equal.
    apply fs_post_empty_locals in H14.
    simpl in H14.
    apply LocalsMap.map_identity_unique; auto.
    destruct (join_ex_units x).
    simpl. eapply unit_identity; eauto.

    simpl fst in H22.
    replace x with (fst (snd wF)).
    eapply pred_nec_hereditary with wF; auto.
    destruct wF as [wFn wF'].
    rewrite world_nec_split; split; auto.
    replace wFn with (fst w).
    apply rt_trans with (fst q).
    apply rt_trans with n'.
    replace (fst w) with (fst w2).
    apply Rt_Rft. change (laterR (fst w2) n').
    rewrite later_nat; auto.
    destruct H1.
    destruct H1.
    auto.
    destruct q; rewrite world_nec_split in Hq; destruct Hq; auto.
    apply Rt_Rft. change (laterR (fst q) n'0).
    rewrite later_nat; auto.
    simpl in H0; destruct H0. auto.
    destruct wF'; auto.

    eapply join_canc; eauto.
    assert (fst (snd w) = fst (snd w2)).
    destruct H1.
    destruct H28.
    apply fs_pre_empty_locals in Hpre.
    apply Hpre in H28.
    auto.
    unfold world, mem, locals, LocalsMap.map, MemMap.map in *.
    rewrite H28.
    auto.

  rewrite <- sepcon_assoc in H16.
  revert H16. apply split_sepcon.
  rewrite wand_sepcon_adjoint. hnf; auto.
  hnf; auto.

  eapply Hg; simpl; auto.

  repeat intro. rewrite FF_sepcon in H3. elim H3.

  spec Hsat (make_locals vals fd) (snd (snd w2)).
  spec Hsat (n',(make_locals vals fd,snd (snd w2))).
  spec Hsat; auto.
  spec Hsat.

  exists (n',(make_locals vals fd,snd (snd wpre'))).
  exists (n',(proj1_sig (join_ex_units (make_locals vals fd)),snd (snd w))).
  split.
  split. simpl. split; auto.
  simpl snd.
  split.
  simpl fst.
  destruct (join_ex_units (make_locals vals fd)); auto.
  simpl snd.
  destruct H1. destruct H2; auto.
  split.
  unfold func_pre.
  exists vals.
  exists (n',(proj1_sig (join_ex_units (make_locals vals fd)),snd (snd wpre'))).
  exists (n',(make_locals vals fd,proj1_sig (join_ex_units (snd (snd wpre'))))).
  split.
  split. simpl; split; auto.
  simpl snd.
  split.
  destruct (join_ex_units (make_locals vals fd)); auto.
  destruct (join_ex_units (snd (snd wpre'))); auto.
  split.
  replace (proj1_sig (join_ex_units (make_locals vals fd)))
    with (fst (snd wpre')).
  apply pred_nec_hereditary with wpre'; auto.
  destruct wpre'.
  rewrite world_nec_split; split; auto.
  replace n0 with (fst w2).
  rewrite nec_nat. omega.
  destruct H1. destruct H1.
  destruct w; destruct w2; simpl in *; congruence.
  destruct p; auto.

  replace vals with args.
  auto.

  apply list_eval_join_sub with _ _ _ w2 in Hargs; eauto.
  apply list_eval_evaluate_exprs in Hargs.
  eapply evaluate_exprs_fun; eauto.

  apply LocalsMap.map_identity_unique; auto.
  apply (fs_pre_empty_locals fs) in Hpre; auto.
  destruct (join_ex_units (make_locals vals fd)).
  simpl. eapply unit_identity; eauto.

  apply make_locals_func_start_locals.
  destruct (join_ex_units (snd (snd (wpre')))).
  simpl. eapply unit_identity; eauto.

  split; auto.
  simpl.
  destruct (join_ex_units (make_locals vals fd)).
  simpl.
  eapply unit_identity; eauto.

  eapply Hsat; eauto.

  rewrite Hfd in H11. discriminate.
Qed.

Lemma hoare_call' : forall ps R i f es fs Q,
  satisfies_fun_spec ps f fs |--
  hoare_ ps R
     (EX vals:list val, list_eval es vals &&
       EX a:fs_A fs,
         fs_pre fs a vals *
         defined i *
         All v:val,
           fs_post fs a v * hasval i v -* Q)
     (call i f es)
     Q.
Proof.
  intros.
  cut (TT |--
  satisfies_fun_spec ps f fs -->
  hoare_ ps R
     (EX vals:list val, list_eval es vals &&
       EX a:fs_A fs,
         fs_pre fs a vals *
         defined i *
         All v:val,
           fs_post fs a v * hasval i v -* Q)
     (call i f es)
     Q).
  intros.
  rewrite <- imp_andp_adjoint in H.
  rewrite TT_and in H. auto.
  rewrite <- hoare_fact.
  intros n ?.
  apply hoare_call.
Qed.

Lemma hoare_if : forall ps R e P c1 c2 Q n,
  hoare_ ps R (EX v:nat, eval e (int_val v) && !!(v <> 0) && P) c1 Q n ->
  hoare_ ps R (eval e (int_val 0) && P) c2 Q n ->

  hoare_ ps R
      (EX v:nat, eval e (int_val v) && P)
      (cif e c1 c2)
      Q n.
Proof.
  intros.
  do 10 intro.
  rewrite exp_sepcon1 in H4.
  destruct H4 as [v ?].
  destruct H4 as [w1 [w2 [? [? ?]]]].
  destruct H5.
  assert (eval e (int_val v) a'0).
  simpl. simpl in H5.
  destruct e; simpl in H5.
  simpl.
  eapply e; eauto.
  destruct H4. destruct H8; eauto.
  destruct (eq_nat_dec v 0).

  subst v.
  spec H0 b b0 a' H1 H2.
  spec H0 rho m a'0 H3.
  spec H0.
  exists w1. exists w2.
  intuition.
  split; auto.
  repeat intro.
  destruct n'. simpl in H10. subst.
  constructor 2. econstructor.
  constructor.
  eapply step_if_false; eauto.
  simpl in H10. destruct H10 as [st'' [? ?]].
  inv H10. inv H17.
  apply H0 with n'; auto. omega.
  elim H21.
  hnf in H5; congruence.

  spec H b b0 a' H1 H2.
  spec H rho m a'0 H3.
  spec H.
  exists w1; exists w2.
  intuition.
  exists v. split; auto.
  split; auto.
  repeat intro.
  destruct n'. simpl in H10. subst.
  constructor 2. econstructor.
  constructor.
  eapply step_if_true; eauto.
  simpl in H10. destruct H10 as [st'' [? ?]].
  inv H10. inv H17.
  elim n0.
  hnf in H5; congruence.
  apply H with n'; auto. omega.
Qed.


Lemma hoare_assign : forall ps R i e Q n,
   hoare_ ps R
     (EX v:val, eval e v && (defined i * (hasval i v -* Q)))
     (assign i e)
     Q n.
Proof.
  intros. apply hoare_straight. intros.
  rewrite exp_sepcon1 in H0.
  destruct H0 as [v ?].
  rewrite andp_com in H0.
  apply eval_up' in H0.
  destruct H0.
  rewrite sepcon_assoc in H0.
  apply defined_update with (v:=v) in H0.
  destruct H0 as [rho' [? ?]].
  exists rho'. exists m.
  split.
  econstructor; eauto.
  hnf in H1.
  auto.
  revert H2.
  rewrite <- sepcon_assoc.
  apply split_sepcon.
  rewrite sepcon_comm.
  rewrite wand_sepcon_adjoint. hnf; auto.
  hnf; auto.
Qed.

Lemma hoare_store : forall ps R e1 e2 Q n,
  hoare_ ps R
     (EX a:addr, EX v:val,
       eval e1 (ptr_val a) &&
       eval e2 v &&
       ( (EX vold:val, mapsto a Share.top vold) *
         (mapsto a Share.top v -* Q) ))
     (store e1 e2)
     Q n.
Proof.
  intros. apply hoare_straight. intros.
  rename H into Hn. rename H0 into H.
  rewrite exp_sepcon1 in H.
  destruct H as [a ?].
  rewrite exp_sepcon1 in H.
  destruct H as [v' ?].
  rewrite andp_com in H.
  rewrite <- andp_assoc in H.
  apply eval_up in H.
  destruct H.
  apply eval_up' in H.
  destruct H.
  rewrite exp_sepcon1 in H.
  rewrite exp_sepcon1 in H.
  destruct H as [v ?].
  rewrite sepcon_assoc in H.
  eapply mapsto_update with (v:=v) (v':=v') in H.
  destruct H as [m' [? ?]].
  exists rho. exists m'.
  split.
  econstructor; eauto.
  hnf in H1; auto.
  hnf in H0; auto.
  generalize H2.
  rewrite <- sepcon_assoc.
  apply split_sepcon.
  rewrite sepcon_comm.
  rewrite wand_sepcon_adjoint. hnf; auto.
  hnf; auto.
Qed.

Lemma hoare_load : forall ps R i e Q n,
  hoare_ ps R
     (EX a:addr, EX sh:Share.t, EX v:val,
                  eval e (ptr_val a) &&
                  ((mapsto a sh v * defined i) *
                   ((mapsto a sh v * hasval i v) -* Q)))
     (load i e)
     Q n.
Proof.
  intros. apply hoare_straight. intros.
  rename H into Hn. rename H0 into H.
  rewrite exp_sepcon1 in H.
  destruct H as [a ?].
  rewrite exp_sepcon1 in H.
  destruct H as [sh ?].
  rewrite exp_sepcon1 in H.
  destruct H as [v ?].
  rewrite andp_com in H.
  apply eval_up' in H.
  destruct H.
  rewrite (sepcon_comm _ (defined i)) in H.
  repeat rewrite sepcon_assoc in H.
  apply defined_update with (v:=v) in H.
  destruct H as [rho' [? ?]].
  exists rho'. exists m.
  split.
  econstructor; eauto.
  hnf in H0. eauto.
  rewrite sepcon_comm in H1.
  repeat rewrite sepcon_assoc in H1.
  eapply mapsto_val; eauto.
  repeat rewrite <- sepcon_assoc in H1.
  generalize H1.
  apply split_sepcon.
  rewrite (sepcon_comm (hasval i v) _).
  rewrite sepcon_comm.
  rewrite wand_sepcon_adjoint. hnf; auto.
  hnf; auto.
Qed.

Lemma hoare_seq : forall ps R P1 c1 P2 c2 P3 n,
  hoare_ ps R P1 c1 P2 n ->
  hoare_ ps R P2 c2 P3 n ->
  hoare_ ps R P1 (seq c1 c2) P3 n.
Proof.
  intros. do 10 intro.
  spec H (kseq c2 b) b0 a' H1.
  spec H0 b b0 a' H1.
  destruct H2.
  spec H0. split; auto.
  spec H. split; auto.
  apply rguards_unwind with b a'; auto.
  spec H (fst (snd a'0)) (snd (snd a'0)).
  spec H a'0.
  spec H.
  destruct a'0.
  rewrite world_nec_split; split; auto.
  rewrite world_nec_split in H3. destruct H3; auto.
  destruct p; auto.
  spec H; auto.
  repeat intro.
  destruct n'; simpl in H7.
  subst st'.
  constructor 2. econstructor.
  econstructor. econstructor.
  destruct H7 as [st'' [? ?]].
  inv H7. inv H14.
  spec H n'. spec H. omega.
  eapply H; eauto.
Qed.

Lemma hoare_while : forall ps R e c I n,
  hoare_ ps R
     (EX v:nat, eval e (int_val v) && !!(v <> 0) && I)
     c
     (EX v:nat, eval e (int_val v) && I) n ->

  hoare_ ps R
     (EX v:nat, eval e (int_val v) && I)
     (while e c)
     (eval e (int_val 0) && I) n.
Proof.
  intros.
  induction n using (well_founded_induction lt_wf).
  do 10 intro.
  destruct H4 as [w1 [w2 [? [? ?]]]].
  destruct H5 as [v [? ?]].
  destruct H2.
  assert (eval e (int_val v) a'0).
  simpl in H5; simpl.
  destruct e. simpl in H5; simpl.
  eapply e; eauto.
  destruct H4. destruct H9; eauto.

  destruct (eq_nat_dec v 0).
  subst v.

  spec H8 (fst (snd a'0)) (snd (snd a'0)).
  spec H8 a'0.
  spec H8.
  destruct a'0.
  rewrite world_nec_split; split; auto.
  rewrite world_nec_split in H3; destruct H3; auto.
  destruct p; auto.

  spec H8; auto.
  exists w1; exists w2; intuition.
  split; auto.

  repeat intro.
  destruct n'; simpl in H11.
  subst st'. constructor 2.
  econstructor. econstructor.
  eapply step_while_false. auto.
  destruct H11 as [st'' [? ?]].
  inv H11. inv H18.
  apply H8 with n'; auto. omega.

  hnf in H9. rewrite H9 in H22.
  elim H17. congruence.

  repeat intro.
  destruct n'; simpl in H11.
  subst st'. constructor 2.
  do 2 econstructor.
  eapply step_while_true; eauto.
  destruct H11 as [st'' [? ?]].
  inv H11. inv H18.
  hnf in H9. rewrite H9 in H21. elim n0. congruence.
  hnf in H9. rewrite H9 in H22. inv H22.
  spec H0 n'. spec H0.
  apply lt_le_trans with (fst a'0).
  omega.
  rewrite <- nec_nat.
  apply rt_trans with a'; auto.
  destruct a'0. rewrite world_nec_split in H3; destruct H3; auto.
  spec H0; auto.
  apply pred_nec_hereditary with n; auto.
  rewrite nec_nat.
  apply le_trans with (fst a'0).
  omega.
  rewrite <- nec_nat.
  apply rt_trans with a'; auto.
  destruct a'0. rewrite world_nec_split in H3; destruct H3; auto.

  spec H (kseq (while e c) b) b0 n'.
  spec H.
  rewrite nec_nat.
  apply le_trans with (fst a'0).
  omega.
  rewrite <- nec_nat.
  apply rt_trans with a'; auto.
  destruct a'0. rewrite world_nec_split in H3; destruct H3; auto.

  spec H.
  split.
  apply rguards_unwind with b a'; auto.
  rewrite nec_nat.
  apply le_trans with (fst a'0).
  omega.
  rewrite <- nec_nat.
  destruct a'0. rewrite world_nec_split in H3; destruct H3; auto.

  spec H0 b b0 n'.
  spec H0; auto.
  spec H0.
  split. apply pred_nec_hereditary with a'; auto.

  rewrite nec_nat.
  apply le_trans with (fst a'0).
  omega.
  rewrite <- nec_nat.
  destruct a'0. rewrite world_nec_split in H3; destruct H3; auto.

  apply pred_nec_hereditary with a'; auto.

  rewrite nec_nat.
  apply le_trans with (fst a'0).
  omega.
  rewrite <- nec_nat.
  destruct a'0. rewrite world_nec_split in H3; destruct H3; auto.
  auto.

  spec H (fst (snd a'0)) (snd (snd a'0)).
  spec H (n',(fst (snd a'0),snd (snd a'0))).
  spec H; auto.
  spec H.
  exists (n',snd w1).
  exists (n',snd w2).
  split.
  split. split; auto.
  simpl snd.
  destruct H4. destruct a'0; auto.
  split.
  exists x.
  split. split; auto.
  apply pred_nec_hereditary with w1; auto.
  destruct w1. rewrite world_nec_split; split; auto.
  replace n1 with (fst a'0).
  rewrite nec_nat. omega.
  destruct H4. destruct H4.
  symmetry; destruct w2; etransitivity; eassumption.

  apply pred_nec_hereditary with w2; auto.
  destruct w2. rewrite world_nec_split; split; auto.
  replace n1 with (fst a'0).
  rewrite nec_nat. omega.
  destruct H4. destruct H4. auto.

  apply H with n'; auto.
Qed.

Lemma hoare_consequence : forall ps R R' P P' c Q Q' n,
  hoare_ ps R P c Q n ->
  lift (Q --> Q') n ->
  lift (P' --> P) n ->
  lift (All v:val, R v --> R' v) n ->
  hoare_ ps R' P' c Q' n.
Proof.
  intros.
  intros k F w H3 [H4 H5].
  spec H k F w H3. spec H.
  split.
  intros e rho m w' H6 H7.
  eapply H4; eauto.
  rewrite exp_sepcon1.
  rewrite exp_sepcon1 in H7.
  destruct H7. exists x.
  destruct H7 as [w1 [w2 [? [? ?]]]].
  exists w1; exists w2; intuition.
  destruct H8.
  split; auto.
  apply H2 with (fst (snd w1)) (snd (snd w1)); auto.
  destruct w1.
  rewrite world_nec_split; split; auto.
  apply rt_trans with w; auto.
  replace n0 with (fst w').
  destruct w'.
  rewrite world_nec_split in H6; destruct H6; auto.
  destruct H7. destruct H7; destruct w'; destruct w2; simpl in *; congruence.
  destruct p; auto.

  intros rho m w' H6 H7.
  eapply H5; eauto.
  destruct H7 as [w1 [w2 [? [? ?]]]].
  exists w1; exists w2; intuition.
  apply H0 with (fst (snd w1)) (snd (snd w1)); auto.
  destruct w1.
  rewrite world_nec_split; split; auto.
  apply rt_trans with w; auto.
  replace n0 with (fst w').
  destruct w'.
  rewrite world_nec_split in H6; destruct H6; auto.
  destruct H7. destruct H7; destruct w'; destruct w2; simpl in *; congruence.
  destruct p; auto.

  intros rho m w' H6 H7.
  eapply H; eauto.
  destruct H7 as [w1 [w2 [? [? ?]]]].
  exists w1; exists w2; intuition.
  apply H1 with (fst (snd w1)) (snd (snd w1)); auto.

  destruct w1.
  rewrite world_nec_split; split; auto.
  apply rt_trans with w; auto.
  replace n0 with (fst w').
  destruct w'.
  rewrite world_nec_split in H6; destruct H6; auto.
  destruct H7. destruct H7; destruct w'; destruct w2; simpl in *; congruence.
  destruct p; auto.
Qed.

Lemma hoare_while_wp : forall ps R e c Q,
  TT |-- hoare_ ps R
     (EX I:pred world,
        (lift_nat
        (hoare_ ps R
             (EX v:nat, eval e (int_val v) && !!(v <> 0) && I)
             c
             (EX v:nat, eval e (int_val v) && I))) *
         (lift_nat (lift (eval e (int_val 0) && I --> Q))) *
        (EX v:nat, eval e (int_val v) && I))
     (while e c)
     Q.
Proof.
  intros. rewrite hoare_ex.
  intros n H I.
  rewrite sepcon_assoc.
  rewrite hoare_fact.
  rewrite hoare_fact.
  do 6 intro.
  apply hoare_consequence with R
    (EX  v : nat, eval e (int_val v) && I)
    (eval e (int_val 0) && I); auto.
  apply hoare_while.
  apply pred_nec_hereditary with a'; auto.
  repeat intro; auto.
  repeat intro; auto.
Qed.
