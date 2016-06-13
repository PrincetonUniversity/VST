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
Require Import sepcomp.semantics.
Require Import sepcomp.extspec.
Require Import floyd.proofauto.

(* Variables to be instantiated once the program is known. *)
Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _lock_t := 2%positive. (* 2 is the number given by
clightgen when threads.h is included first *)

Variable voidstar_funtype : type.
Definition tlock := Tstruct _lock_t noattr.
(* Notation tlock := tuint (only parsing). *)

Axiom lock_inv : share -> val -> mpred -> mpred.

Axiom lock_inv_share_join : forall sh1 sh2 sh v R, sepalg.join sh1 sh2 sh ->
  (lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R)%logic.

Axiom lock_inv_isptr : forall sh v R, (`(lock_inv sh v R) |-- !!(isptr v))%logic.

Axiom lock_hold : share -> val -> mpred.

(*+ Deep embedding of [mpred]s *)

Inductive Pred :=
  | Mapsto :  Share.t -> type -> val -> val -> Pred
  | Mapsto_ :  Share.t -> type -> val -> Pred
  | Data_at : forall cs : compspecs, Share.t -> forall t : type, reptype t -> val -> Pred
  | Data_at_ : forall cs : compspecs, Share.t -> type -> val -> Pred
  | Lock_hold : Share.t -> val -> Pred
  | Lock_inv : Share.t -> val -> Pred -> Pred
  | Pred_prop : Prop -> Pred
  | Exp : forall A : Type, (A -> Pred) -> Pred
  | Pred_list : list Pred -> Pred.

Fixpoint Interp (p : Pred) : mpred :=
  match p with
  | Mapsto a b c d => mapsto a b c d
  | Mapsto_ a b c => mapsto_ a b c
  | Data_at a b c d e => @data_at a b c d e
  | Data_at_ a b c d => @data_at_ a b c d
  | Lock_inv a b c => lock_inv a b (Interp c)
  | Lock_hold a b => lock_hold a b
  | Pred_prop a => prop a
  | Exp a b => exp (fun x => Interp (b x))
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
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R).

Definition acquire_oracular_spec :=
  mk_funspecOracle
    Oracle
    (* ARGS *)
    ([(_lock, tptr tlock)], tvoid)
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
         SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R)
       end).

Definition release_spec :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v (Interp R)).

Definition release_oracular_spec :=
  mk_funspecOracle
    Oracle
    (* ARGS *)
    ([(_lock, tptr tlock)], tvoid)
    cc_default
    (* WITH *)
    (Oracle * val * share * Pred)
    (* PRE *)
    (fun (x : Oracle * val * share * Pred) (oracle : Oracle) =>
       match x with
         (oracle_x, v, sh, R) =>
         PROP (oracle = oracle_x; readable_share sh)
         LOCAL (temp _lock v)
         SEP (lock_inv sh v (Interp R); lock_hold Share.top v; Interp R)
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
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v).

Definition freelock_spec cs :=
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (writable_share sh)
     LOCAL (temp _lock v)
     SEP (lock_inv sh v (Interp R); lock_hold Share.top v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v).

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
          (ty *                     (* WITH we call spawn with *)
          (ty -> val -> Pred) *       (* precondition *)
          (ty -> val -> Pred))%type}  (* postcondition *)
   PRE [_f OF tptr voidstar_funtype, _args OF tptr tvoid]
     PROP ()
     LOCAL (temp _args b)
     SEP
     (EX _y : ident, EX globals : list (ident * val),
      match PrePost with existT ty (_, pre, post) =>
      (func_ptr'
        (WITH y : val, x : ty
          PRE [ _y OF tptr tvoid ]
            PROP ()
            (LOCALx (temp _y y :: map (fun x => gvar (fst x) (snd x)) globals)
            (SEP   (Interp (pre x y))))
          POST [tptr tvoid]
            PROP  ()
            LOCAL ()
            SEP   (Interp (post x y)))
       f)
      end;
      match PrePost with existT ty (w, pre, post) =>
      Interp (pre w b)
      end)
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

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (* (ext_link "makelock"%string, makelock_spec cs) :: *)
  (* (ext_link "freelock"%string, freelock_spec cs) :: *)
  (* (ext_link "spawn"%string, spawn_spec) :: *)
  nil.

Definition concurrent_oracular_ext_spec (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecsOracle_rec
    ext_link
    (ok_void_spec (list rmap)).(@OK_ty)
    (ok_void_spec (list rmap)).(@OK_spec)
    (concurrent_oracular_specs cs ext_link).

Definition concurrent_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_specs cs ext_link).

Definition Concurrent_Oracular_Espec cs ext_link :=
  Build_OracleKind
    (list rmap)
    (concurrent_oracular_ext_spec cs ext_link).

Definition Concurrent_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_ext_spec Z cs ext_link).

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
  jsafeN (Concurrent_Espec unit cs ext_link).(@OK_spec) ge n tt c m ->
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
      (* all: match goal with E : _ = 1%positive |- _ => admit end. *)
    }
    
    assert (Ex : exists name sig, e = EF_external name sig) by (destruct e; eauto; tauto).
    destruct Ex as (name & sg & ->); clear Hef.
    
    Unset Printing Implicit.
    Local Notation "{| 'JE_spec ... |}" := {| JE_spec := _; JE_pre_hered := _; JE_post_hered := _; JE_exit_hered := _ |}.
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
                 @jsafeN (list rmap) (concurrent_oracular_ext_spec cs ext_link) ge (S n) []
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
