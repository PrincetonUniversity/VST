Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.

Require Import msl.eq_dec.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import sepcomp.semantics.
Require Import concurrency.semax_conc.

(* Require Import sepcomp.semantics. *)

(** * Concurrent machine:
   - union of all memories
   - resource pool: None if locked | Some resource if unlocked
   - list of threads (corestate, memory) *)

Record concurrent_machine := build_cm
  { cm_env : genv;
    cm_mem : juicy_mem;
    cm_res : list (Address.address * (mpred * option rmap));
    cm_thd : list (corestate * rmap) }.

Definition joins_list (m : list rmap) :=
  forall i j mi mj,
    i <> j ->
    nth_error m i = Some mi ->
    nth_error m j = Some mj ->
    joins mi mj.

Fixpoint filter_option_list {A} (l : list (option A)) : list A :=
  match l with
  | None :: l => filter_option_list l
  | Some x :: l => x :: filter_option_list l
  | nil => nil
  end.

(* lemmas about joining: consider using existing results in lockfree/ecm *)
Fixpoint join_to (ms : list rmap) (s : rmap) : Prop :=
  match ms with
    nil => app_pred emp s
  | m :: ms => exists s', join m s' s /\ join_to ms s'
  end.

(** * How resources are related to resources in dry/wet memories *)

Inductive cohere_res_lock : forall (resv : option (mpred * option rmap)) (wetv : resource) (dryv : memval), Prop :=
| cohere_notlock wetv dryv:
    (forall R, ~islock_pred R wetv) ->
    cohere_res_lock None wetv dryv
| cohere_locked R wetv :
    islock_pred R wetv ->
    cohere_res_lock (Some (R, None)) wetv (Byte (Integers.Byte.zero))
| cohere_unlocked R phi wetv :
    islock_pred R wetv ->
    R phi ->
    cohere_res_lock (Some (R, Some phi)) wetv (Byte (Integers.Byte.one)).

(* todo: change association lists (alists) to compcert's Maps *)

Fixpoint alist_get {A B} {E : EqDec A} (a : A) (l : list (A * B)) : option B :=
  match l with
    nil => None
  | (x, y) :: l => if eq_dec x a then Some y else alist_get x l
  end.

Definition alist_update {A B} (a : A) (b : B) (l : list (A * B)) : list (A * B) := (a, b) :: l.

Fixpoint update_nth {A} (n : nat) (a : A) (l : list A) : list A :=
  match n, l with
    _, nil => nil
  | 0, x :: l => a :: l
  | S n, x :: l => x :: (update_nth n a l)
  end.

(** * Invariant for safe concurrent machines:
   1) all rmaps join to the main memory's rmap
   2) locks and resource invariants in the resource pool correspond to:
      - invariants in wet memory
      - values in dry memory
   3) all threads are safe for n steps *)

Definition cm_joins
           (res : list (Address.address * (mpred * option rmap)))
           (thd : list (corestate * rmap)) jm
  := join_to (filter_option_list (map snd (map snd res)) ++ map snd thd) (m_phi jm).

Definition invariant Jspec (n : nat) (cm : concurrent_machine) : Prop :=
  match cm with
  | build_cm env jm res thd =>
    cm_joins res thd jm /\
    (forall lock : Address.address,
        cohere_res_lock
          (alist_get lock res)
          (m_phi jm @ lock)
          (contents_at (m_dry jm) lock)) /\
    (forall i q m, forall ora : Oracle, nth_error thd i = Some (q, m) -> semax.jsafeN Jspec env n ora q jm)
  end.

Open Scope string_scope.

(** * Initial machine *)

Definition initial_cm {CS V G ext_link}
        (prog : program) (m : Memory.mem)
        (SP : @semax_prog (Concurrent_Oracular_Espec CS ext_link) CS prog V G)
        (Hmem : Genv.init_mem prog = Some m)
        (n : nat) : concurrent_machine :=
  let spr := semax_prog_rule (Concurrent_Oracular_Espec CS ext_link) V G prog m SP Hmem in
  let q : corestate := projT1 (projT2 spr) in
  let jm : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n) in
  {| cm_mem := jm; cm_env := globalenv prog; cm_res := nil; cm_thd := (q, m_phi jm) :: nil |}.

Lemma invariant_initial_cm {CS V G ext_link}
        (prog : program) (m : Memory.mem)
        (SP : @semax_prog (Concurrent_Oracular_Espec CS ext_link) CS prog V G)
        (Hmem : Genv.init_mem prog = Some m)
        (n : nat) : invariant (concurrent_oracular_ext_spec CS ext_link) n (initial_cm prog m SP Hmem n).
Proof.
  unfold initial_cm.
  set (spr := semax_prog_rule (Concurrent_Oracular_Espec CS ext_link) V G prog m SP Hmem).
  set (q := projT1 (projT2 spr)).
  set (jm := proj1_sig (snd (projT2 (projT2 spr)) n)).
  split;[|split].
  - (* joining condition *)
    exists (core (m_phi jm)); simpl.
    split; admit.
    (* Questions:
      - why is emp better that "empty_rmap"? it requires "identity", but I thought we had no identity?
      - isn't core the corresponding neutral element? I can't find a lemma about that
     *)
    (* exists (empty_rmap n); split. *)
    (* destruct spr as (b' & q' & Hb & JS); simpl projT1 in *; simpl projT2 in *. *)
    (* unfold join. *)
    (* now admit (* join with empty_rmap -- doable *). *)
    (* now admit. *)
  
  - (* cohere_res_lock (there are no locks at first) *)
    constructor.
    intros.
    match goal with |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & notlock) end.
    intro.
    eapply notlock; eexists; eauto.
    
  - (* safety of the only thread *)
    intros i q0 m0 oracle E.
    destruct i as [ | [ | i ]]; simpl in E; inversion E; subst.
    destruct spr as (b' & q' & Hb & JS); simpl projT1 in *; simpl projT2 in *.
    destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl projT1 in *; simpl projT2 in *.
    subst.
    simpl snd.
    (* apply (S oracle). *) 
Admitted. (* faster *)
(*
Qed.  (* 1'40 --- Definition + Lemma faster than Program Definition *)
 *)

(* todo move those signatures to semax_conc *)
Definition acquire_sig :=
  {| sig_args := AST.Tint :: nil;
     sig_res := None;
     sig_cc := cc_default |}.
Definition release_sig := acquire_sig.
Definition makelock_sig := acquire_sig.
Definition freelock_sig := acquire_sig.
Definition spawn_sig := 
  {| sig_args := AST.Tint :: AST.Tint :: nil;
     sig_res := None;
     sig_cc := cc_default |}.

Definition thd_update (thd thd' : list (corestate * rmap)) i x x' :=
  nth_error thd i = Some x /\
  nth_error thd' i = Some x' /\
  forall j,
    i <> j ->
    (nth_error thd j = None /\
     nth_error thd j = None) \/
    (exists c phi phi',
       necR phi phi' /\
       nth_error thd' j = Some (c, phi) /\
       nth_error thd' j = Some (c, phi')).

Import Mem.

Definition jm_rel_rmap (phi : rmap) (jm jm' : juicy_mem) :=
  (m_dry jm).(mem_contents) = (m_dry jm').(mem_contents) /\
  m_phi jm' = phi.

Definition jm_rel_rmaps (phis : list rmap) (jm jm' : juicy_mem) :=
  exists phi, join_to phis phi /\ jm_rel_rmap phi jm jm'.

Definition same_dry jm jm' := (m_dry jm).(mem_contents) = (m_dry jm').(mem_contents).

Definition update_dry jm jm' b ofs v v' :=
  Mem.load Mint32 (m_dry jm) b (Int.intval ofs) = Some v /\
  Mem.store Mint32 (m_dry jm) b (Int.intval ofs) v' = Some (m_dry jm') /\
  m_phi jm = m_phi jm'.

Require Import veric.res_predicates.

Definition isfunsig A PRE r := exists callingc sh sh' sig Q, r = YES sh sh' (FUN sig callingc) (SomeP (A :: boolT :: environ :: nil) (packPQ PRE Q)).

(* todo move this comment away: schedule rather than lts: we want to run the same thread for internal steps *)
Inductive cm_step : list nat -> concurrent_machine -> list nat -> concurrent_machine -> Prop :=
| cm_step_nil_sched cm :
    cm_step nil cm nil cm

| cm_step_bad_sched i sch cm :
    nth_error cm.(cm_thd) i = None ->
    cm_step (i :: sch) cm sch cm

| cm_step_internal i sch env res thd thd' c c' jm jm' jmi jmi' :
    same_dry jm jmi ->
    same_dry jm' jmi' ->
    cm_joins res thd jm ->
    cm_joins res thd' jm' ->
    thd_update thd thd' i (c, m_phi jmi) (c', m_phi jmi') ->
    corestep (juicy_core_sem cl_core_sem) env c jmi c' jmi' ->
    cm_step
      (i :: sch) (build_cm env jm res thd)
      (i :: sch) (build_cm env jm' res thd')

| cm_step_acquire_failure i sch mem env res thd c cont phi b o R ce te:
    nth_error thd i = Some (c, phi) ->
    c = ExtCall
          (EF_external "acquire" acquire_sig) acquire_sig
          (Values.Vptr b o :: nil)
          None ce te cont ->
    alist_get (b, Int.intval o) res = (Some (R, None)) ->
    cm_step
      (i :: sch) (build_cm env mem res thd)
      sch        (build_cm env mem res thd)
    
| cm_step_acquire_success i sch jm jm' env res res' thd thd' c cont b o R ce te phi phi' phi_acq :
    nth_error thd i = Some (c, phi) ->
    c = ExtCall
          (EF_external "acquire" acquire_sig) acquire_sig
          (Values.Vptr b o :: nil)
          None ce te cont ->
    join phi phi_acq phi' ->
    alist_get (b, Int.intval o) res = Some (R, Some phi_acq) ->
    alist_update (b, Int.intval o) (R, None) res = res' ->
    thd_update thd thd' i (c, phi) (State ce te cont, phi') ->
    update_dry jm jm' b o (Values.Vint Int.one) (Values.Vint Int.zero) ->
    cm_step
      (i :: sch) (build_cm env jm res thd)
      sch        (build_cm env jm' res' thd')

| cm_step_release i sch jm jm' env res res' thd thd' c cont b o R ce te phi phi' phi_rel :
    nth_error thd i = Some (c, phi) ->
    c = ExtCall
          (EF_external "release" release_sig) release_sig
          (Values.Vptr b o :: nil)
          None ce te cont ->
    join phi' phi_rel phi ->
    app_pred R phi_rel ->
    alist_get (b, Int.intval o) res = Some (R, None) ->
    alist_update (b, Int.intval o) (R, Some phi_rel) res = res' ->
    thd_update thd thd' i (c, phi) (State ce te cont, phi') ->
    update_dry jm jm' b o (Values.Vint Int.zero) (Values.Vint Int.one) ->
    cm_step
      (i :: sch) (build_cm env jm res thd)
      sch        (build_cm env jm' res' thd')

| cm_step_spawn i sch jm jm' env res thd thd' c cont f_b f_o arg_b arg_o A a PRE ce te phi phi' phi_spawned genv venv tenv :
    nth_error thd i = Some (c, phi) ->
    c = ExtCall
          (EF_external "spawn" spawn_sig) spawn_sig
          (Values.Vptr f_b f_o :: Values.Vptr arg_b arg_o :: nil)
          None ce te cont ->
    isfunsig A PRE (phi @ (f_b, Int.intval f_o)) ->
    join phi' phi_spawned phi ->
    app_pred (PRE a (mkEnviron genv venv tenv)) phi_spawned ->
    thd_update thd thd' i (c, phi) (State ce te cont, phi') ->
    cm_step
      (i :: sch) (build_cm env jm res thd)
      sch        (build_cm env jm' res (thd ++ (c, phi_spawned) :: nil))
  (* freelock and makelock are similar, we avoid them for now *)
  (* to do: spawn *)
.

(* notes on design choices: an LTS would be an elegant way of handling
  demonic+angelic nondeterminism, but we'd need to consume an entire
  coarse step to consume one label (=piece of schedule) *)

Require Import sepcomp.step_lemmas.

Lemma cm_step_invariant js n cm sch :
  invariant js (S n) cm -> exists cm' sch', cm_step sch cm sch' cm'/\ invariant js n cm'.
Proof.
  destruct cm as [env jm res thd] eqn:Heqcm.
  intros (Hj & lockcoh & safe).
  destruct sch as [ | i sch ].
  
  { (* empty schedule *)
    exists cm, nil; subst; split.
    - constructor.
    - unfold invariant. intuition.
      apply safe_downward1.
      eapply safe; eauto. }
  destruct (nth_error thd i) as [(c, phi)|] eqn:Heqthd_i.
  
  Focus 2.
  { (* bad schedule *)
    exists cm, sch; subst; split.
    - constructor. apply Heqthd_i.
    - unfold invariant; intuition.
      apply safe_downward1.
      eapply safe; eauto. } Unfocus.
  
  destruct c as [ve te k | ef sig args lid ve te k] eqn:Heqc.
  
  { (* thread#i is in some internal step *)
    (* get next state through "jsafeN" with an arbitrary oracle *)
    (* but it should not be jm! *)
    assert (X: exists c' jm', corestep (juicy_core_sem cl_core_sem) env (State ve te k) jm c' jm'). {
      specialize (safe _ _ _ nil Heqthd_i).
      inversion safe; subst.
      - eauto.
      - inversion H0.
      - inversion H.
    }
    destruct X as (c' & jm' & step & decay & lev).
    
    (* todo: make thd' the aged version of all rmaps *)
    pose (thd' := map (fun x : _ * rmap => let (c, phi) := x in (c, age1 phi)) thd).
    clear thd'.
    pose (thd' := thd).
    
    (* building the jm2 out of the jm and phi2 : state a lemma *)
    
    (* oracle : first, replace sig with ex.  Then, either define
    another definition of jsafe or use a dummy oracle and then say (∀Ω
    safe(Ω,c,m)) ∧ (c,m→c',m') → (∀Ω safe(Ω,c',m')) *)
    
    (* also MAX is for compcert to know we're not fucking with e.g.
    constant propagation, and CUR is for the caller to know compcert
    is not writing in temporarily read-only variables sometimes *)
    
    (* todo the differences between interaction semantics and trace
    semantics *)
    
    (* build new state *)
    pose (thd'' := update_nth i (c', m_phi jm') thd').
    
    exists (build_cm env jm' res thd''), (i :: sch).
    split.
    - (* find jm, jmi, ..., then use safety to get one step from jsafe *)
      (* apply cm_step_internal with c c'.
      inversion step.
      + rewrite Heqthd_i, Heqc.
        inversion H.
        Require Import semax_congruence.
        unfold jsafeN, juicy_safety.safeN in Hsafe.
        pose proof (proj1 (safeN_step_jsem_spec _ _ _ _ _ _ _ _) Hsafe).
        apply (proj1 (safeN_step_jsem_spec _ _ _ _ _ _ _ _)) in Hsafe.
       destruct k as [ | [ s | s1 s2 | s1 s2 | | ret f e' te' ] ks].
       *)
      
(*    
Lemma safeN_step_jsem_spec: forall gx vx tx n k jm,
        (forall ora,
            @safeN_
              _ _ _ _ (fun x => Genv.genv_symb (genv_genv x)) juicy_safety.Hrel
              (juicy_core_sem cl_core_sem) OK_spec
              gx (S n) ora (State vx tx k) jm) ->
        exists c' m', (cl_step gx (State vx tx k) (m_dry jm) c' (m_dry m') /\
                  resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi m') /\
                  level jm = S (level m') /\
                  forall ora,
                    @safeN_
                      _ _ _ _ (fun x => Genv.genv_symb (genv_genv x)) juicy_safety.Hrel
                      (juicy_core_sem cl_core_sem) OK_spec gx n ora c' m').
 *)
Admitted.

(* eventually, move the following *)
(* Definition of angelic safety (that we use) and demonic safety (used after erasure) *)

Inductive iter {X} (R : X -> X -> Type) : nat -> (X -> X -> Type) :=
  | iter_O x : iter R O x x
  | iter_S n x y z : R x y -> iter R n y z -> iter R (S n) x z.

Definition dsafe_ n {X} (R : X -> X -> Type) x := forall y m, lt m n -> iter R m x y -> sigT (R y).

Lemma dsafe__det {X} (R : X -> X -> Type) n x y : dsafe_ n R y -> R x y -> (forall y', R x y' -> y = y') -> dsafe_ (1 + n) R x.
Proof.
  intros Sy xy D z m mn xz; inversion xz; subst; eauto.
  assert (lt n0 n) by auto with *.
  rewrite <-(D _ X0) in *; eauto.
Qed.

Lemma dsafe__R {X} (R : X -> X -> Type) n x y : dsafe_ (1 + n) R x -> R x y -> dsafe_ n R y.
Proof.
  intros Sx xy z m mn it.
  edestruct (Sx z (S m)); eauto. auto with *.
  econstructor; eauto.
Qed.

Lemma dsafe_S {X} (R : X -> X -> Type) n x : dsafe_ (1 + n) R x -> dsafe_ n R x.
Proof.
  intros S y m mn; apply S; auto.
Qed.

Definition asafe_ n {X} (R : X -> X -> Type) x := { y : X & iter R n x y }.

Lemma asafe_S {X} (R : X -> X -> Type) n x y : asafe_ n R y -> R x y -> asafe_ (1 + n) R x.
Proof.
  intros [z Hz] r; exists z. econstructor; eauto.
Qed.

(* Lemma : asafe -> det -> dsafe *)

Definition sim {X} (step : X -> X -> Type) (R : nat -> X -> Type) :=
  forall n x, R (S n) x -> {y : _ & (step x y * R n y)%type }.

(*
Lemma invariant_simulation genv oracle : sim cm_step (invariant genv oracle).
Admitted (* hard *).

Lemma invariant_safe : forall n cm, invariant HOLE HOLE n cm -> asafe_ n cm_step cm.
Admitted (* easy *).

Lemma semax_to_machine : (* not sure how to state *)
  semax_prog -> concurrent_machine_safe (initial_concurrent_machine).
Proof.
  intros SP.
  apply invariant_safe.
  apply invariant_initial.
Qed.
*)
