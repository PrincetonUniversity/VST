Require Import msl.msl_standard.
Require Import msl.seplog.
Require Import veric.base.
Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.juicy_mem_ops.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.semax.
Require Import veric.semax_call.
Require Import veric.semax_ext.
Require Import veric.semax_ext_oracle.
Require Import veric.juicy_safety.
Require Import veric.Clight_new.
Require Import veric.res_predicates.
Require Import veric.SeparationLogic.
Require Import sepcomp.semantics.
Require Import sepcomp.extspec.
Require Import floyd.reptype_lemmas.
Require Import floyd.field_at.
Require Import floyd.client_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import concurrency.juicy_machine.

Set Bullet Behavior "Strict Subproofs".

(* Variables to be instantiated once the program is known. *)
Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _lock_t := 3%positive. (* 2 (* 3 -WM *) is the number given by
clightgen when threads.h is included first *)

Definition voidstar_funtype := Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default.
Definition tlock := Tstruct _lock_t noattr.
(* Notation tlock := tuint (only parsing). *)

Definition lock_inv : share -> val -> mpred -> mpred :=
  fun sh v R =>
    (EX b : block, EX ofs : _,
      !!(v = Vptr b ofs) &&
      LKspec
        R
        (Share.unrel Share.Lsh sh)
        (Share.unrel Share.Rsh sh)
        (b, Int.unsigned ofs))%logic.

Definition positive_mpred (R : mpred) :=
  forall phi, app_pred R phi -> exists l sh rsh k p, phi @ l = YES sh rsh k p.

Definition selflock_fun Q sh p : (unit -> mpred) -> (unit -> mpred) :=
  fun R _ => (Q * lock_inv sh p (|> R tt))%logic.

Definition selflock' Q sh p : unit -> mpred := HORec (selflock_fun Q sh p).
Definition selflock Q sh p : mpred := selflock' Q sh p tt.

Definition nonexpansive F := HOnonexpansive (fun P (_ : unit) => F (P tt)).

Lemma nonexpansive_entail F : nonexpansive F -> forall P Q, (P <=> Q |-- F P <=> F Q)%logic.
Proof.
  intros N P Q.
  specialize (N (fun _ => P) (fun _ => Q)).
  eapply derives_trans; [ eapply derives_trans | ]; [ | apply N | ].
  now apply allp_right.
  now apply allp_left.
Qed.

Axiom nonexpansive_lock_inv : forall sh p, nonexpansive (lock_inv sh p).

Lemma lock_inv_later sh p R : lock_inv sh p R |-- lock_inv sh p (|> R)%logic.
Admitted.

Lemma selflock'_eq Q sh p : selflock' Q sh p =
  selflock_fun Q sh p (selflock' Q sh p).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 u.
  apply subp_sepcon; [ apply subp_refl | ].
  eapply derives_trans. apply (nonexpansive_lock_inv sh p).
  apply allp_left with tt, fash_derives, andp_left1, derives_refl.
Qed.

Lemma selflock_eq Q sh p : selflock Q sh p = (Q * lock_inv sh p (|> selflock Q sh p))%logic.
Proof.
  unfold selflock at 1.
  rewrite selflock'_eq.
  reflexivity.
Qed.

(* In fact we need locks to two resources:
   1) the resource invariant, for passing the resources
   2) the join resource invariant, for returning all resources, including itself
   for this we need to define them in a mutually recursive fashion: *)

Definition res_invariants_fun Q sh1 p1 sh2 p2 : (bool -> mpred) -> (bool -> mpred) :=
  fun R b =>
    if b then
      (Q * lock_inv sh2 p2 (|> R false))%logic
    else
      (Q * lock_inv sh1 p1 (|> R true) * lock_inv sh2 p2 (|> R false))%logic.

Definition res_invariants Q sh1 p1 sh2 p2 : bool -> mpred := HORec (res_invariants_fun Q sh1 p1 sh2 p2).
Definition res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 true.
Definition join_res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 false.

Lemma res_invariants_eq Q sh1 p1 sh2 p2 : res_invariants Q sh1 p1 sh2 p2 =
  res_invariants_fun Q sh1 p1 sh2 p2 (res_invariants Q sh1 p1 sh2 p2).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 b.
  destruct b.
    (* resource invariant *)
    apply subp_sepcon; try apply subp_refl.
    apply allp_left with false.
    eapply derives_trans.
      apply nonexpansive_entail, nonexpansive_lock_inv.
      apply fash_derives, andp_left1, derives_refl.
    
    (* join resource invariant *)
    repeat apply subp_sepcon; try apply subp_refl.
      apply allp_left with true.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.
      
      apply allp_left with false.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.
Qed.

Lemma res_invariant_eq Q sh1 p1 sh2 p2 :
  res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2))%logic.
Proof.
  unfold res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

Lemma join_res_invariant_eq Q sh1 p1 sh2 p2 :
  join_res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh1 p1 (|> res_invariant Q sh1 p1 sh2 p2) *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2))%logic.
Proof.
  unfold join_res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

(* Condition variables *)
(*Definition _cond_t := 4%positive.*)
Definition tcond := tint.

(* Does this need to be anything special? *)
Definition cond_var {cs} sh v := @data_at_ cs sh tcond v.


(*+ Deep embedding of [mpred]s *)

Inductive Pred :=
  | Mapsto :  Share.t -> type -> val -> val -> Pred
  | Mapsto_ :  Share.t -> type -> val -> Pred
  | Data_at : forall cs : compspecs, Share.t -> forall t : type, reptype t -> val -> Pred
  | Data_at_ : forall cs : compspecs, Share.t -> type -> val -> Pred
  | Lock_inv : Share.t -> val -> Pred -> Pred
  | Self_lock : Pred -> Share.t -> val -> Pred
  | Res_inv : Pred -> Share.t -> val -> Share.t -> val -> Pred
  | Cond_var : forall cs : compspecs, Share.t -> val -> Pred
  | Pred_prop : Prop -> Pred
  | Exp : forall A : Type, (A -> Pred) -> Pred
  | Later : Pred -> Pred
  | Pred_list : list Pred -> Pred.

Fixpoint Interp (p : Pred) : mpred :=
  match p with
  | Mapsto a b c d => mapsto a b c d
  | Mapsto_ a b c => mapsto_ a b c
  | Data_at a b c d e => @data_at a b c d e
  | Data_at_ a b c d => @data_at_ a b c d
  | Lock_inv a b c => lock_inv a b (Interp c)
  | Self_lock a b c => selflock (Interp a) b c
  | Res_inv a b c d e => res_invariant (Interp a) b c d e
  | Cond_var a b c => @cond_var a b c
  | Pred_prop a => (!!a && emp)%logic
  | Exp a b => exp (fun x => Interp (b x))
  | Later a => later (Interp a)
  | Pred_list l => fold_right sepcon emp (map Interp l)
  end.

(*+ Type of the oracle *)

Definition Oracle := list rmap.

(*+ Specification of each concurrent primitive *)

Definition acquire_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R); Interp R).

Definition acquire_oracular_spec :=
  mk_funspecOracle
    Oracle
    (* ARGS *)
    ((_lock, tptr tlock) :: nil, tvoid)
    cc_default
    (* WITH *)
    (Prop * Oracle * val * share * Pred)
    (* PRE *)
    (fun (x : Prop * Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
       | (ok, oracle_x, v, sh, R) =>
         PROP (readable_share sh;
                 (match oracle with
                  | nil => ~ok
                  | cons mlock oracle' => oracle' = oracle_x /\ (app_pred (Interp R) mlock <-> ok)
                  end))
         LOCAL (temp _lock v)
         SEP (lock_inv sh v (Interp R))
       end)
    (* POST *)
    (fun (x : Prop * Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (ok, oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; ok)
         LOCAL ()
         SEP (lock_inv sh v (Interp R); Interp R)
       end).

Definition release_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh; precise (Interp R); positive_mpred (Interp R))
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R); Interp R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R)).

Definition release_oracular_spec :=
  mk_funspecOracle
    Oracle
    (* ARGS *)
    ((_lock, tptr tlock) :: nil, tvoid)
    cc_default
    (* WITH *)
    (Oracle * val * share * Pred)
    (* PRE *)
    (fun (x : Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; readable_share sh)
         LOCAL (temp _lock v)
         SEP (lock_inv sh v (Interp R); Interp R)
       end)
    (* POST *)
    (fun (x : Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; readable_share sh)
         LOCAL ()
         SEP (lock_inv sh v (Interp R))
       end).

Definition makelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (@data_at_ cs sh tlock v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R)).

Definition freelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh; positive_mpred (Interp R))
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R); Interp R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v; Interp R).

(* Notes about spawn_thread:

As in makelock/acquire/... we get a universe inconsistency when we add
"WITH P" to the specification.  This universe inconsistency will
eventually disappear in a different model for rmaps tracking
covariance and contravariance.  In the meantime, we use a the deep
embedding [Pred] and an embedding [PrePost] of the pre- and
post-condition depending on Type term [ty].

The spawned function has for argument name [_y], which is
existentially quantified.  The function also can use a list of global
variables [globals].

For now, the specification of the spawned function has to be exactly
of the form that you can see below (inside the "match PrePost ...").
Cao Qinxiang is working on a notion of sub-specification that might
enable us to have smoother specifications.

The postcondition might not be emp, so we have potential memory leaks
when a thread exists (those maps are still handled by the concurrent
machine).

To enable joinable threads, the postcondition would be [tptr tthread]
with a type [tthread] related to the postcondition through a [thread]
predicate in the logic.  The [join] would then also be implemented
using the oracle, as [acquire] is.  The postcondition would be [match
PrePost with existT ty (w, pre, post) => thread th (Interp (post w b))
end] *)

Definition spawn_spec :=
  WITH f : val,
       b : val,
       PrePost :
         { ty : Type &
          (ty *                     (* WITH clause for spawned function *)
          (ty -> val -> Pred))%type}  (* precondition (postcondition is emp) *)
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP (
       match PrePost with
         existT ty (w, pre) =>
         forall phi,
           app_pred (Interp (pre w b)) phi ->
           almost_empty phi
       end
     )
     LOCAL (temp _args b)
     SEP
     (match PrePost with existT ty (_, pre) =>
      EX _y : ident, EX globals : ty -> list (ident * val),
      (func_ptr'
        (WITH y : val, x : ty
          PRE [ _y OF tptr tvoid ]
            PROP ()
            (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) (globals x))
            (SEP   (Interp (pre x y))))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   (emp))
       f)
      end;
        match PrePost with
          existT ty (w, pre) =>
          Interp (pre w b)
      end
     )
   POST [ tvoid  ]
     PROP  ()
     LOCAL ()
     SEP   (emp).

(*+ Adding the specifications to a void ext_spec *)


(*! The void ext_spec *)
Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False) 
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition concurrent_oracular_specs (cs : compspecs) (ext_link : string -> ident) := 
  (ext_link "acquire"%string, acquire_oracular_spec) ::
  (ext_link "release"%string, release_oracular_spec) ::
  nil.

Definition concurrent_simple_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  nil.

Definition concurrent_oracular_ext_spec (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecsOracle_rec
    ext_link
    (ok_void_spec (list rmap)).(@OK_ty)
    (ok_void_spec (list rmap)).(@OK_spec)
    (concurrent_oracular_specs cs ext_link).

Definition concurrent_simple_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_simple_specs cs ext_link).

Definition Concurrent_Oracular_Espec cs ext_link :=
  Build_OracleKind
    (list rmap)
    (concurrent_oracular_ext_spec cs ext_link).

Definition Concurrent_Simple_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_simple_ext_spec Z cs ext_link).

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, lt i n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Set Printing Implicit.
Require Import sepcomp.step_lemmas.

Lemma at_external_not_halted (G C M : Type) (csem : semantics.CoreSemantics G C M) (q : C) :
  semantics.at_external csem q <> None -> semantics.halted csem q = None.
Proof.
  destruct (@semantics.at_external_halted_excl G C _ csem q); tauto.
Qed.

Theorem oracular_refinement cs ext_link ge n oracle c m :
  jsafeN (Concurrent_Simple_Espec unit cs ext_link).(@OK_spec) ge n tt c m ->
  jsafeN (Concurrent_Oracular_Espec cs ext_link).(@OK_spec) ge n oracle c m.
Proof.
  revert oracle c m; induction n as [n InductionHypothesis] using strong_nat_ind; intros oracle c m.
  intros Safe; induction Safe as [ | | n z_unit c m e sig args x E Pre Post | ].
  all: swap 3 4.
  - (* safeN_0 *)
    now eapply safeN_0; eauto.
  
  - (* safeN_step *)
    eapply safeN_step; eauto.
    now apply InductionHypothesis; auto.
  
  - (* safeN_halted *)
    now eapply safeN_halted; eauto.
  
  - (* safeN_external *)
    destruct c as [ | ef_ sig_ args_ lid ve te k ]; [ discriminate | ].
    simpl in E; injection E as -> -> -> .
    
    (* We need to know which of the externals we are talking about *)
    (* paragraph below: ef has to be an EF_external *)
    assert (Hef : match e with EF_external _ _ => True | _ => False end).
    {
      match goal with x : ext_spec_type _ _  |- _ => clear -x end.
      destruct e eqn:Ee; [ apply I | .. ]; simpl in x;
        repeat match goal with
                 _ : context [ oi_eq_dec ?x ?y ] |- _ =>
                 destruct (oi_eq_dec x y); try discriminate; try tauto
               end.
    }
    
    assert (Ex : exists name sig, e = EF_external name sig) by (destruct e; eauto; tauto).
    destruct Ex as (name & sg & ->); clear Hef.
    
    Unset Printing Implicit.
    revert x Pre Post.
    simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
    unfold funspec2pre, funspec2post, ext_spec_type, ext_spec_pre, ext_spec_post.
    destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg)))
    (* destruct (ident_eq (ext_link "acquire"%string) (ef_id ext_link (EF_external name sg))) *)
      as [ H_acquire | notacquire ].
    
    { (* case 1 : acquire *)
      intros [phi_x [[vx shx] Rx]] Pre Post.
      destruct oracle as [ | phi_oracle oracle ].
      
      - simpl.
        
        (* this is the x parameter for the WITH clause, but it has the wrong type. *)
        pose (xwith := (phi_x, (False, @nil rmap, vx, shx, Rx))).
        assert ((rmap * (Prop * list rmap * val * share * Pred) =
                 @ext_spec_type
                   juicy_mem external_function (@OK_ty (Concurrent_Oracular_Espec cs ext_link))
                   (@OK_spec (Concurrent_Oracular_Espec cs ext_link)) (EF_external name sg))
               )%type as EqT.
        { simpl. rewrite H_acquire. simpl. if_tac;[ reflexivity | congruence ]. }
        
        (* getting a JMeq-copy of x of the correct type *)
        remember xwith as x2.
        assert (JMeq xwith x2). subst. apply JMeq_refl.
        clear Heqx2.
        revert x2 H.
        pattern (rmap * (Prop * list rmap * val * share * Pred))%type at 1 3.
        cut (
            (fun T : Type =>
               forall x2 : T,
                 @JMeq (rmap * (Prop * list rmap * val * share * Pred)) xwith T x2 ->
                 @jsafeN (list rmap) (concurrent_oracular_ext_spec cs ext_link) ge (S n) nil
                         (Clight_new.ExtCall (EF_external name sg) sig args lid ve te k) m)
              (@ext_spec_type juicy_mem external_function (@OK_ty (Concurrent_Oracular_Espec cs ext_link))
                              (@OK_spec (Concurrent_Oracular_Espec cs ext_link)) (EF_external name sg))).
        {
          assert (APP : forall P Q  : Prop, P = Q -> P -> Q) by (intros ? ? -> ; auto).
          apply APP.
          rewrite <- EqT.
          reflexivity.
        }
        intros x2 E2.
        
        Set Printing All.
        (* The following is strange, it fails to typecheck even though
        it is provided as a quote from one of the types. *)
        Fail apply safeN_external with
          (e := EF_external name sg)
          (x := x2).
        Fail 
          set (qwdq := @ext_spec_type juicy_mem external_function (list rmap)
                                      (JE_spec (list rmap) (concurrent_oracular_ext_spec cs ext_link))
                                      acquire_oracular_spec).
        Unset Printing All.
        
        eapply safeN_external with
          (e := EF_external name sg)
            (x := x2).
        + reflexivity.
        + simpl.
          
          revert x2 E2.
          simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
          unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
          destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg))).
          2:congruence. clear e.
          intros x2 E2. apply JMeq_eq in E2. subst x2.
          unfold xwith; simpl in Pre |- *. (* done with JMeq.. for this +bullet. *)
          
          destruct Pre as [phi0 [phi1 [Hj [[[? ?] [[? ?] ?]] ?]]]].
          exists phi0, phi1; repeat split; auto.
          
        + intros ret m' z' n' Hn Hr.
          specialize (Post ret m' tt n' Hn Hr).
          
          revert x2 E2.
          simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
          unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
          destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg))).
          2:congruence. clear e.
          intros x2 E2. apply JMeq_eq in E2. subst x2.
          
          intros [phi0 [phi1 [Hj PLS]]].
          destruct PLS as [[[? [FALSE ?]] ?] ?].
          exfalso; tauto.
      
      - simpl.
        
        (* this is the x parameter for the WITH clause, but it has the wrong type. *)
        pose (xwith := (phi_x, (app_pred (Interp Rx) phi_oracle, oracle, vx, shx, Rx))).
        assert ((rmap * (Prop * list rmap * val * share * Pred) =
                 @ext_spec_type
                   juicy_mem external_function (@OK_ty (Concurrent_Oracular_Espec cs ext_link))
                   (@OK_spec (Concurrent_Oracular_Espec cs ext_link)) (EF_external name sg))
               )%type as EqT.
        { simpl. rewrite H_acquire. simpl. if_tac;[ reflexivity | congruence ]. }
        
        (* getting a JMeq-copy of x of the correct type *)
        remember xwith as x2.
        assert (JMeq xwith x2). subst. apply JMeq_refl.
        clear Heqx2.
        revert x2 H.
        pattern (rmap * (Prop * list rmap * val * share * Pred))%type at 1 3.
        cut (
            (fun T : Type =>
               forall x2 : T,
                 @JMeq (rmap * (Prop * list rmap * val * share * Pred)) xwith T x2 ->
                 @jsafeN (list rmap) (concurrent_oracular_ext_spec cs ext_link) ge (S n) (phi_oracle :: oracle)
                         (Clight_new.ExtCall (EF_external name sg) sig args lid ve te k) m)
              (@ext_spec_type juicy_mem external_function (@OK_ty (Concurrent_Oracular_Espec cs ext_link))
                              (@OK_spec (Concurrent_Oracular_Espec cs ext_link)) (EF_external name sg))).
        {
          assert (APP : forall P Q  : Prop, P = Q -> P -> Q) by (intros ? ? -> ; auto).
          apply APP.
          rewrite <- EqT.
          reflexivity.
        }
        intros x2 E2.
        
        eapply safeN_external with
          (e := EF_external name sg)
            (x := x2).
        + reflexivity.
        + simpl.
          
          revert x2 E2.
          simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
          unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
          destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg))).
          2:congruence. clear e.
          intros x2 E2. apply JMeq_eq in E2. subst x2.
          
          unfold xwith; simpl in Pre |- *.
          
          destruct Pre as [phi0 [phi1 [Hj [[[? ?] [[? ?] ?]] ?]]]].
          exists phi0, phi1; repeat split; auto.
          
        + intros ret m' z' n' Hn Hr.
          specialize (Post ret m' tt n' Hn Hr).
          
          revert x2 E2.
          simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
          unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
          destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg))).
          2:congruence. clear e.
          intros x2 E2. apply JMeq_eq in E2. subst x2.
          
          intros [phi0 [phi1 [Hj [[? [? Sep]] NC]]]].
          destruct Post as [c' [Ae Post]].
          { exists phi0, phi1; repeat split; auto. }
          exists c'; split; [ now auto | ].
          apply InductionHypothesis. omega.
          hnf.
          destruct z_unit. (* only unit (can be replaced with a universal quantification) *)
          apply Post.
    }
    
    unfold JE_spec.
    unfold funspec2jspec, funspec2extspec.
    simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
    unfold funspec2pre, funspec2post, ext_spec_type, ext_spec_pre, ext_spec_post, release_spec.
    
    destruct (oi_eq_dec (Some (ext_link "release"%string)) (ef_id ext_link (EF_external name sg)))
      as [ H_release | notrelease ].
    { (* case 2: release *)
      intros [phi_x [[vx shx] Rx]] Pre Post.
      simpl.
      
      (* this is the x parameter for the WITH clause, but it has the wrong type. *)
      pose (xwith := (phi_x, (oracle, vx, shx, Rx))).
      assert ((rmap * (list rmap * val * share * Pred) =
               @ext_spec_type
                 juicy_mem external_function (@OK_ty (Concurrent_Oracular_Espec cs ext_link))
                 (@OK_spec (Concurrent_Oracular_Espec cs ext_link)) (EF_external name sg))
             )%type as EqT.
      simpl in *.
      { rewrite H_release. simpl. if_tac. congruence. if_tac. reflexivity. congruence. }
      
      (* getting a JMeq-copy of x of the correct type *)
      remember xwith as x2.
      assert (JMeq xwith x2). subst. apply JMeq_refl.
      clear Heqx2.
      revert x2 H.
      simpl OK_ty.
      pattern (rmap * (list rmap * val * share * Pred))%type at 1 3.
      cut (
          (fun T : Type =>
             forall x2 : T,
               @JMeq (rmap * (list rmap * val * share * Pred)) xwith T x2 ->
               @jsafeN (list rmap) (concurrent_oracular_ext_spec cs ext_link) ge (S n) oracle
                       (Clight_new.ExtCall (EF_external name sg) sig args lid ve te k) m)
            (@ext_spec_type juicy_mem external_function (@OK_ty (Concurrent_Oracular_Espec cs ext_link))
                            (@OK_spec (Concurrent_Oracular_Espec cs ext_link)) (EF_external name sg))).
      {
        assert (APP : forall P Q  : Prop, P = Q -> P -> Q) by (intros ? ? -> ; auto).
        apply APP.
        rewrite <- EqT.
        reflexivity.
      }
      intros x2 E2.
      
      eapply safeN_external with
      (e := EF_external name sg)
        (x := x2).
      + reflexivity.
      + simpl.
        revert x2 E2.
        
        simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
        unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
        destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg))).
        now congruence.
        simpl (JE_spec _ _).
        simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
        unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
        destruct (oi_eq_dec (Some (ext_link "release"%string)) (ef_id ext_link (EF_external name sg))).
        2:congruence. clear e.
        intros x2 E2. apply JMeq_eq in E2. subst x2.
        
        unfold xwith; simpl in Pre |- *.
        
        destruct Pre as [phi0 [phi1 [Hj [[[? ?] [[? ?] ?]] ?]]]].
        exists phi0, phi1; repeat split; auto.
        
      + intros ret m' z' n' Hn Hr.
        specialize (Post ret m' tt n' Hn Hr).
        
        revert x2 E2.
        simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
        unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
        destruct (oi_eq_dec (Some (ext_link "acquire"%string)) (ef_id ext_link (EF_external name sg))).
        now congruence.
        simpl (JE_spec _ _).
        simpl (ext_spec_pre _); simpl (ext_spec_post _); simpl (ext_spec_type _).
        unfold funspecOracle2pre, funspecOracle2post, ext_spec_type, ext_spec_pre, ext_spec_post.
        destruct (oi_eq_dec (Some (ext_link "release"%string)) (ef_id ext_link (EF_external name sg))).
        2:congruence. clear e.
        intros x2 E2. apply JMeq_eq in E2. subst x2.
        
        intros [phi0 [phi1 [Hj [[? [? Sep]] NC]]]].
        destruct Post as [c' [Ae Post]].
        { exists phi0, phi1; repeat split; auto. }
        exists c'; split; [ now auto | ].
        apply InductionHypothesis. omega.
        hnf.
        destruct z_unit.
        apply Post.
    }
    
    { (* remaining of cases *)
      intros x; exfalso; tauto.
    }
Qed.


(*
Lemma semax_conc' cs (ext_link: string -> ident) id sig cc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspecOracle Oracle sig cc A P Q in
  In (ext_link id, f) fs ->
  list_norepet (map fst fs) ->
  (forall n,
      semax_external_oracle
        (Concurrent_Espec cs ext_link) (fst (split (fst sig)))
        (EF_external id (funsig2signature sig cc)) _ P Q n).
Proof.
  intros.
  apply semax_ext'_oracle; auto.
Qed.

Lemma semax_conc cs (ext_link: string -> ident) id ids sig sig' cc A P Q :
  let fs := threadspecs cs ext_link in
  let f := mk_funspecOracle Oracle sig  cc A P Q in
  In (ext_link id,f) fs ->
  list_norepet (map fst fs) ->
  ids = fst (split (fst sig)) ->
  sig' = funsig2signature sig cc ->
  (forall n, semax_external_oracle (Concurrent_Espec cs ext_link) ids (EF_external id sig') _ P Q n).
Proof.
  intros.
  subst.
  apply semax_conc'; hnf; auto.
Qed.
 *)

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "spawn"%string, spawn_spec) ::
  nil.

Definition concurrent_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_specs cs ext_link).

Definition Concurrent_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_ext_spec Z cs ext_link).
