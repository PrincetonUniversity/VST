Load loadpath.
Require Import veric.base.
Require Import compcert.Events.

(* A "core semantics represents" a fairly traditional,
   sequential, small step semantics of computation.  They
   are designed to cooperate with "extensions"
   which give semantics to primtive constructs not defined
   by the extensible semantics (e.g., external function calls).

   The [G] type parameter is the type of global environments,
   the type [C] is the type of core states, and the type [E]
   is the type of extension requests.  The [at_external]
   function gives a way to determine when the sequential
   execution is blocked on an extension call, and to extract
   the data necessary to execute the call.  [after_external]
   give a way to inject the extension call results back into
   the sequential state so execution can continue.
   
   [make_initial_core] produces the core state corresponding
   to an entry point of the program.  The arguments are the
   program's genv, a pointer to the function to run, and
   the arguments for that function.

   The [safely_halted] predicate indicates when a program state
   has reached a halted state, and what it's exit code is
   when it has reached such a state.

   [corestep] is the fundamental small-step relation for
   the sequential semantics.

   The remaining properties give basic sanity properties which constrain
   the behavior of programs.
    1) a state cannot be both blocked on an extension call
        and also step,
    2) a state cannot both step and be halted
    3) a state cannot both be halted and blocked on an external call
 *)

Record CoreSemantics {G C M D:Type}: Type :=
  { initial_mem: G -> M -> D -> Prop;
    (*characterizes initial memories; 
       type D stands for the type of initialization data, 
       eg list (ident * globvar V)*)
  make_initial_core : G -> val -> list val -> option C;
  at_external : C -> option (external_function * signature * list val);
  after_external : option val -> C -> option C;
  safely_halted : G -> C -> option int; (*maybe delete this, too?*)
  corestep : G -> C -> M -> C -> M -> Prop;

  corestep_not_at_external: forall ge m q m' q', 
    corestep ge q m q' m' -> at_external q = None;

  corestep_not_halted: forall ge m q m' q', 
    corestep ge q m q' m' -> safely_halted ge q = None;

  at_external_halted_excl: forall ge q, 
    at_external q = None \/ safely_halted ge q = None
  }.
Implicit Arguments CoreSemantics [].

(* Definition of multistepping. *)
Section corestepN.
  Context {G C M E D:Type} (Sem:CoreSemantics G C M D) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
    | O => fun c m c' m' => (c,m) = (c',m')
    | S k => fun c1 m1 c3 m3 => exists c2, exists m2,
               corestep Sem ge c1 m1 c2 m2 /\
               corestepN k c2 m2 c3 m3
    end.

  Lemma corestepN_add : forall n m c1 m1 c3 m3,
    corestepN (n+m) c1 m1 c3 m3 <->
    exists c2, exists m2,
      corestepN n c1 m1 c2 m2 /\
      corestepN m c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m x x0 c3 m3).
    apply H in H2. 
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m x1 x2 c3 m3). 
    eauto.
  Qed.

  Definition corestep_plus c m c' m' :=
    exists n, corestepN (S n) c m c' m'.

  Definition corestep_star c m c' m' :=
    exists n, corestepN n c m c' m'.

  Lemma corestep_plus_star : forall c1 c2 m1 m2,
       corestep_plus c1 m1 c2 m2 -> corestep_star c1 m1 c2 m2.
   Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma corestep_plus_trans : forall c1 c2 c3 m1 m2 m3,
       corestep_plus c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 -> corestep_plus c1 m1 c3 m3.
   Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
        destruct (corestepN_add (S n1) (S n2) c1 m1 c3 m3) as [_ H].
        eexists. apply H. exists c2. exists m2. split; assumption.
   Qed.

  Lemma corestep_star_plus_trans : forall c1 c2 c3 m1 m2 m3,
       corestep_star c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 -> corestep_plus c1 m1 c3 m3.
   Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
        destruct (corestepN_add n1 (S n2) c1 m1 c3 m3) as [_ H]. rewrite <- plus_n_Sm in H.
        eexists. apply H.  exists c2. exists m2.  split; assumption.
   Qed.

  Lemma corestep_plus_star_trans: forall c1 c2 c3 m1 m2 m3,
         corestep_plus c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 -> corestep_plus c1 m1 c3 m3.
   Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
        destruct (corestepN_add (S n1) n2 c1 m1 c3 m3) as [_ H]. rewrite plus_Sn_m in H.
        eexists. apply H.  exists c2. exists m2.  split; assumption.
   Qed.

   Lemma corestep_star_trans: forall c1 c2 c3 m1 m2 m3, 
        corestep_star c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 -> corestep_star c1 m1 c3 m3.
   Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
        destruct (corestepN_add n1 n2 c1 m1 c3 m3) as [_ H]. 
        eexists. apply H.  exists c2. exists m2.  split; assumption.
   Qed.

   Lemma corestep_plus_one: forall c m c' m',
       corestep  Sem ge c m c' m' -> corestep_plus c m c' m'.
     Proof. intros. unfold corestep_plus, corestepN. simpl.
          exists O. exists c'. exists m'. eauto. 
     Qed.

   Lemma corestep_plus_two: forall c m c' m' c'' m'',
       corestep  Sem ge c m c' m' -> corestep  Sem ge c' m' c'' m'' -> corestep_plus c m c'' m''.
     Proof. intros. 
          exists (S O). exists c'. exists m'. split; trivial. 
          exists c''. exists m''. split; trivial. reflexivity.
     Qed.

   Lemma corestep_star_zero: forall c m, corestep_star  c m c m.
     Proof. intros. exists O. reflexivity.  
     Qed.

   Lemma corestep_star_one: forall c m c' m',
       corestep  Sem ge c m c' m' -> corestep_star c m c' m'.
     Proof. intros. 
          exists (S O). exists c'. exists m'. split; trivial. reflexivity. 
     Qed.

   Lemma corestep_plus_split: forall c m c' m',
       corestep_plus c m c' m' ->
       exists c'', exists m'', corestep  Sem ge c m c'' m'' /\ corestep_star c'' m'' c' m'.
     Proof. intros.
         destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*. 
         exists c2. exists m2. split. assumption. exists n. assumption.  
     Qed.

End corestepN.

(* A minimal preservation property we sometimes require.
 
 Commented out when moving to forward_simulation eq/inj/ext *)
(*Definition mem_forward (m1 m2:mem) :=
  (forall b, Mem.valid_block m1 b ->
      Mem.valid_block m2 b /\ 
       forall ofs, Mem.perm m1 b ofs Max = Mem.perm m2 b ofs Max).
*)
Definition mem_forward (m1 m2:mem) :=
  (forall b, Mem.valid_block m1 b ->
      Mem.valid_block m2 b /\ 
       forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p).

Lemma external_call_mem_forward:
  forall (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem),
  external_call ef ge vargs m1 t vres m2 -> mem_forward m1 m2.
  Proof.
    intros.
    intros b Hb.
    split; intros. eapply external_call_valid_block; eauto.
      eapply external_call_max_perm; eauto.
  Qed.

(*
 This predicate restricts what coresteps are allowed
   to do.  Essentially, a corestep can only store, allocacte
   and free, and must do so respecting permissions.*) 
Definition allowed_core_modification (m1 m2:mem) :=
  mem_forward m1 m2 /\
  (forall b ofs p,
    Mem.perm m1 b ofs Cur p ->
    (Mem.perm m2 b ofs Cur p) \/
    (Mem.perm m1 b ofs Cur Freeable /\ forall p', ~Mem.perm m2 b ofs Cur p')) /\
  (forall b ofs p,
    Mem.valid_block m1 b ->
    Mem.perm m2 b ofs Cur p ->
    Mem.perm m1 b ofs Cur p) /\
  (forall b ofs' n vs,
    Mem.loadbytes m1 b ofs' n = Some vs ->
      (Mem.loadbytes m2 b ofs' n = Some vs) \/
      (exists ofs, ofs' <= ofs < ofs' + n /\ Mem.perm m1 b ofs Cur Writable)).

(* The kinds of extensible semantics used by CompCert.  Memories are
   CompCert memories and external requests must contain external functions.
 *)
Record CompcertCoreSem {G C D} :=
{ csem :> CoreSemantics G C mem D

; csem_corestep_fun: forall ge m q m1 q1 m2 q2, 
       corestep csem ge q m q1 m1 ->
       corestep csem ge q m q2 m2 -> 
          (q1, m1) = (q2, m2)

; csem_allowed_modifications :
    forall ge c m c' m',
      corestep csem ge c m c' m' ->
      allowed_core_modification m m'
}.
Implicit Arguments CompcertCoreSem [ ].


Lemma corestepN_fun (G C D:Type) (CSem:CompcertCoreSem G C D) :
  forall ge n c m c1 m1 c2 m2,
    corestepN CSem ge n c m c1 m1 ->
    corestepN CSem ge n c m c2 m2 ->
    (c1,m1) = (c2,m2).
Proof.
  induction n; simpl; intuition (try congruence).
  decompose [ex and] H. clear H.
  decompose [ex and] H0. clear H0.
  assert ((x,x0) = (x1,x2)).
  eapply csem_corestep_fun; eauto.
  inv H0.
  eapply IHn; eauto.
Qed.

Inductive entry_points_compose: 
  list (val*val*signature) -> list (val*val*signature) -> 
  list (val*val*signature) -> Prop :=
| EPC1: forall v1 v2 v3 sig r1 r2 r3, 
  entry_points_compose r1 r2 r3 ->
  entry_points_compose ((v1,v2,sig)::r1) ((v2,v3,sig)::r2) ((v1,v3,sig)::r3)
| EPC0: entry_points_compose nil nil nil.

(* Here we present a module type which expresses the sort of forward simulation
   lemmas we have avalaible.  The idea is that these lemmas would be used in
   the individual compiler passes and the composition lemma would be used
   to build the main lemma.
 *)

(*
Module Type SIMULATIONS.
*)
Axiom allowed_core_modification_refl : forall m,
  allowed_core_modification m m.

Axiom allowed_core_modification_trans : forall m1 m2 m3,
  allowed_core_modification m1 m2 ->
  allowed_core_modification m2 m3 ->
  allowed_core_modification m1 m3.

Axiom free_allowed_core_mod : forall m1 b lo hi m2,
  Mem.free m1 b lo hi = Some m2 ->
  allowed_core_modification m1 m2.

Axiom alloc_allowed_core_mod : forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2,b) ->
  allowed_core_modification m1 m2.

Axiom store_allowed_core_mod : forall m1 chunk v b ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 ->
  allowed_core_modification m1 m2.

Hint Resolve 
  allowed_core_modification_refl
  allowed_core_modification_trans
  free_allowed_core_mod
  alloc_allowed_core_mod
  store_allowed_core_mod : allowed_mod.

(* First a forward simulation for passes which do not alter the memory
     layout at all. *)
Module Sim_eq.
Section Forward_simulation_equals. 
  Context {G1 C1 D1 G2 C2 D2:Type}
          {Sem1 : CompcertCoreSem G1 C1 D1}
          {Sem2 : CompcertCoreSem G2 C2 D2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_equals :=
  { core_data:Type;

    match_core : core_data -> C1 -> C2 -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m st1' m', corestep Sem1 ge1 st1 m st1' m' ->
      forall d st2, match_core d st1 st2 ->
        exists st2', exists d',
          match_core d' st1' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord d' d);

   (*LENB: Maybe this should be reformulated so that
      make_initial_core Sem1 ge1 v1 vals = Some c1 implies
       existence of some c2 with 
          make_initial_core Sem2 ge2 v2 vals = Some c2 /\  match_core cd c1 c2?*)
    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals,
          Forall2 (Val.has_type) vals (sig_args sig) ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_core cd c1 c2;

    core_halted : forall cd c1 c2 (v:int),
      match_core cd c1 c2 ->
      safely_halted Sem1 ge1 c1 = Some v ->
      safely_halted Sem2 ge2 c2 = Some v;

    core_at_external : 
      forall d st1 st2 e args ef_sig,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,ef_sig,args) ->
        ( at_external Sem2 st2 = Some (e,ef_sig,args) /\
          Forall2 Val.has_type args (sig_args ef_sig) );

    core_after_external :
      forall d st1 st2 ret e args ef_sig,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,ef_sig,args) ->
        at_external Sem2 st2 = Some (e,ef_sig,args) ->
        Forall2 Val.has_type args (sig_args ef_sig) ->
        Val.has_type ret (proj_sig_res ef_sig) ->
        exists st1', exists st2', exists d',
          after_external Sem1 (Some ret) st1 = Some st1' /\
          after_external Sem2 (Some ret) st2 = Some st2' /\
          match_core d' st1' st2'
  }.
End Forward_simulation_equals. 

Implicit Arguments Forward_simulation_equals [[G1] [C1] [G2] [C2]].
End Sim_eq.

Module Sim_ext.

(* Next, an axiom for passes that allow the memory to undergo extension. *)
Section Forward_simulation_extends. 
  Context {G1 C1 D1 G2 C2 D2:Type}
          {Sem1 : CompcertCoreSem G1 C1 D1}
          {Sem2 : CompcertCoreSem G2 C2 D2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record Forward_simulation_extends := {
    core_data : Type;

    match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2;

    core_halted : 
      forall cd st1 m1 st2 m2 (v:int),
        match_state cd st1 m1 st2 m2 ->
        safely_halted Sem1 ge1 st1 = Some v ->
          safely_halted Sem2 ge2 st2 = Some v /\
          Mem.extends m1 m2;

    core_at_external : 
      forall cd st1 m1 st2 m2 e vals1 ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
          at_external Sem2 st2 = Some (e,ef_sig,vals2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' ef_sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        at_external Sem2 st2 = Some (e,ef_sig,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args ef_sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' -> (*ie spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res ef_sig) -> 

        exists st1', exists st2', exists cd',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'
   }.
End Forward_simulation_extends.

Implicit Arguments Forward_simulation_extends [[G1] [C1] [G2] [C2]].
End Sim_ext.

Module Sim_inj.
(* An axiom for passes that use memory injections. *)
Section Forward_simulation_inject. 
  Context {F1 V1 C1 D1 G2 C2 D2:Type}
          {Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 D1}
          {Sem2 : CompcertCoreSem G2 C2 D2}

          {ge1: Genv.t F1 V1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

Record Forward_simulation_inject := {
    core_data : Type;
    match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop;

    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

(*Maybe we need an axiom like this?
    thread_axiom: forall cd j m1 c1 m2 c2, match_state cd j c1 m1 c2 m2 ->
             (*we want maybe same sequence of memops to be applied in both forward_modifications*)
               allowed_forward_modifications m1 m1' ->
               allowed_forward_modifications m2 m2' ->
           exists j', incject_incr j j' /\ inject_separated j j' m1 m2
               match_state cd j' c1 m1' c2 m2';

    match_state_siminj :
      forall cd j st1 m1 st2 m2,
        match_state cd j st1 m1 st2 m2 -> siminj (injlist_compose j) m1 m2;
*)
    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);

    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          (*Is this line needed?? (forall w1 w2 sigg,  In (w1,w2,sigg) entry_points -> val_inject j w1 w2) ->*)
           Forall2 (val_inject j) vals1 vals2 ->

          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists cd, exists c2, (*exists vals2, exists m2, *)
            make_initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state cd j c1 m1 c2 m2;

(* Attempt to specify forking, parametric in some join relation. It'll be up to the concurrency machine 
to decide hoe memory is split - here we just assume ther are splits for all num_passes memories.
Also, we probably want to allow forking only at (exactly at?) at_external points, and also
add fiuther hypotheses that allows us to carry on in both threads without waiting for after-external,
ie we probably want to add mem_square and some toher hypotheses from after_external somewhere here*)
 (*
    core_at_fork : forall (join:mem -> mem -> mem -> Prop) v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals1 vals2 (m1:mem) js ms m1l m1r m2l m2r msl msr cd c1 c2 c1',
          let m2 := last ms m1 in
          let m2l := last msl m1l in
          let m2r := last msr m1r in

            match_state cd js c1 m1 c2 m2 ->
            join m1l m1r m1 ->
            Forall3 (lift_join join) msl msr ms ->
           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           (*Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->*)

          Forall2 (val_inject js) vals1 vals2 ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          make_initial_core Sem1 ge1 v1 vals1 = Some c1' ->
          exists cd', exists c2', 
            make_initial_core Sem2 ge2 v2 vals2 = Some c2' /\
            match_state cd js c1 m1l c2 m2l /\
            match_state cd' js c1' m1r c2' m2r;
*)
    core_halted : forall cd j c1 m1 c2 m2 (v1:int),
      match_state cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         Mem.inject j m1 m2);

    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1 ef_sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,ef_sig,vals1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ (*LENB: also added meminj_preserves_global HERE*)
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args ef_sig) /\
          at_external Sem2 st2 = Some (e,ef_sig,vals2));

    core_after_external :
      forall cd j j' st1 st2 m1 e vals1 (*vals2*) ret1 m1' m2 m2' ret2 ef_sig,
        Mem.inject j m1 m2->
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
(*     at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->*)

(* LENB: I added meminj_preserves_globals ge1 j as another asumption here,
      in order to get rid of the unprovable Lemma meminj_preserved_globals_inject_incr stated below. 
     The introduction of meminj_preserves_globals ge1 require specializing G1 to (Genv.t F1 V1).
      In principle, we could also specialize G2 to (Genv.t F1 V1).
      Note tha tthis specialization is only done for of CompCertCoreSem's, while
       CoreSem's stay parametric in G1/G2*)
        meminj_preserves_globals ge1 j -> 

        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         mem_unchanged_on (loc_unmapped j) m1 m1' ->
         mem_forward m2 m2' -> 
         mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
         Val.has_type ret2 (proj_sig_res ef_sig) -> 

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'
    }.

End Forward_simulation_inject. 

(*Implicit Arguments Forward_simulation_inject [[G1] [C1] [G2] [C2]].*)
Implicit Arguments Forward_simulation_inject [[F1][V1] [C1] [G2] [C2]].
End Sim_inj.

(*
Section PRECISE_MATCH_PROGRAM.
(*Adapted  from Compcert.AST.MATCH_PROGRAM - but we think we actually don't need this notion, 
hence have commented the coresponding c;lauses below in cc_eq and cc_ext.*)

Variable F1 F2 V1 V2: Type.

Inductive precise_match_funct_entry: ident * F1 -> ident * F2 -> Prop :=
  | precise_match_funct_entry_intro: forall id fn1 fn2,
       precise_match_funct_entry (id, fn1) (id, fn2).

Inductive precise_match_var_entry: ident * globvar V1 -> ident * globvar V2 -> Prop :=
  | precise_match_var_entry_intro: forall id info1 info2 init ro vo,
      precise_match_var_entry (id, mkglobvar info1 init ro vo)
                      (id, mkglobvar info2 init ro vo).

Definition precise_match_program  (P1: AST.program F1 V1)  (P2: AST.program F2 V2) : Prop :=
                (list_forall2 precise_match_funct_entry P1.(prog_funct) (P2.(prog_funct))) /\
                (list_forall2 precise_match_var_entry P1.(prog_vars) (P2.(prog_vars))) /\ 
                P2.(prog_main) = P1.(prog_main).

End PRECISE_MATCH_PROGRAM.
*)

Lemma forall_inject_val_list_inject: forall j args args' (H:Forall2 (val_inject j) args args' ),   val_list_inject j args args'.
  Proof.
    intros j args.
    induction args; intros;  inv H; constructor; eauto.
  Qed. 
Lemma val_list_inject_forall_inject: forall j args args' (H:val_list_inject j args args'), Forall2 (val_inject j) args args' .
  Proof.
    intros j args.
    induction args; intros;  inv H; constructor; eauto.
  Qed. 

Lemma forall_lessdef_val_listless: forall args args' (H: Forall2 Val.lessdef args args'),  Val.lessdef_list args args' .
  Proof.
    intros args.
    induction args; intros;  inv H; constructor; eauto.
  Qed. 
Lemma val_listless_forall_lessdef: forall args args' (H:Val.lessdef_list args args'), Forall2 Val.lessdef args args' .
  Proof.
    intros args.
    induction args; intros;  inv H; constructor; eauto.
  Qed. 


Module CompilerCorrectness.
Definition globvar_eq {V1 V2: Type} (v1:globvar V1) (v2:globvar V2) :=
    match v1, v2 with mkglobvar _ init1 readonly1 volatile1, mkglobvar _ init2 readonly2 volatile2 =>
                        init1 = init2 /\ readonly1 =  readonly2 /\ volatile1 = volatile2
   end.

Inductive external_description :=
   extern_func: signature -> external_description
| extern_globvar : external_description.

Definition entryPts_ok  {F1 V1 F2 V2:Type}  (P1 : AST.program F1 V1)    (P2 : AST.program F2 V2) 
                                       (ExternIdents : list (ident * external_description)) (entryPts: list (val * val * signature)): Prop :=
          forall e d, In (e,d) ExternIdents ->
                              exists b, Genv.find_symbol  (Genv.globalenv P1) e = Some b /\
                                             Genv.find_symbol (Genv.globalenv P2) e = Some b /\
                                             match d with
                                                      extern_func sig => In (Vptr b Int.zero,Vptr b Int.zero, sig) entryPts /\
                                                                                     exists f1, exists f2, Genv.find_funct_ptr (Genv.globalenv P1) b = Some f1 /\ 
                                                                                                                      Genv.find_funct_ptr (Genv.globalenv P2) b = Some f2
                                                    | extern_globvar  => exists v1, exists v2, Genv.find_var_info  (Genv.globalenv P1) b = Some v1 /\
                                                                                                                    Genv.find_var_info  (Genv.globalenv P2) b = Some v2 /\
                                                                                                                    globvar_eq v1 v2
                                             end.

Definition entryPts_inject_ok  {F1 V1 F2 V2:Type}  (P1 : AST.program F1 V1)    (P2 : AST.program F2 V2)  (j: meminj)
                                       (ExternIdents : list (ident * external_description)) (entryPts: list (val * val * signature)): Prop :=
          forall e d, In (e,d) ExternIdents ->
                              exists b1, exists b2, Genv.find_symbol (Genv.globalenv P1) e = Some b1 /\
                                                                Genv.find_symbol (Genv.globalenv P2) e = Some b2 /\
                                                                j b1 = Some(b2,0) /\
                                             match d with
                                                      extern_func sig => In (Vptr b1 Int.zero,Vptr b2 Int.zero, sig) entryPts /\
                                                                                     exists f1, exists f2, Genv.find_funct_ptr (Genv.globalenv P1) b1 = Some f1 /\ 
                                                                                                                      Genv.find_funct_ptr (Genv.globalenv P2) b2 = Some f2
                                                    | extern_globvar  => exists v1, exists v2, Genv.find_var_info  (Genv.globalenv P1) b1 = Some v1 /\
                                                                                                                    Genv.find_var_info  (Genv.globalenv P2) b2 = Some v2 /\
                                                                                                                    globvar_eq v1 v2
                                             end.

Definition externvars_ok  {F1 V1:Type}  (P1 : AST.program F1 V1) 
                                             (ExternIdents : list (ident * external_description)) : Prop :=
         forall b v, Genv.find_var_info  (Genv.globalenv P1) b = Some v -> 
                        exists e, Genv.find_symbol (Genv.globalenv P1) e = Some b /\ In (e,extern_globvar) ExternIdents.

Definition GenvHyp {F1 V1 F2 V2} 
               (P1 : AST.program F1 V1) (P2 : AST.program F2 V2): Prop :=
       (forall id : ident,
                                 Genv.find_symbol (Genv.globalenv P2) id =
                                 Genv.find_symbol (Genv.globalenv P1) id)
       /\ (forall b : block,
                                          block_is_volatile (Genv.globalenv P2) b =
                                          block_is_volatile (Genv.globalenv P1) b).

Inductive compiler_correctness (I: forall F C V  (Sem : CompcertCoreSem (Genv.t F V) C  (list (ident * globvar V)))  (P : AST.program F V),Prop)
        (ExternIdents: list (ident * external_description)):
       forall (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2), Type :=
   cc_eq : forall  (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
 (*              (match_prog:  precise_match_program F1 F2 V1 V2 P1 P2)*)
               (Eq_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_vars)->
                     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_vars)
                                        /\ m1 = m2))
               entrypoints
               (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
               (R:Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints), 
               prog_main P1 = prog_main P2 -> 

(*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
               GenvHyp P1 P2 ->

                I _ _ _  Sem1 P1 -> I _ _ _  Sem2 P2 -> 
               compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 |  cc_ext : forall  (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
(*               (match_prog:  precise_match_program F1 F2 V1 V2 P1 P2)*)
               (Extends_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_vars)->
                     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_vars) 
                                        /\ Mem.extends m1 m2))
               entrypoints
               (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
               (R:Sim_ext.Forward_simulation_extends _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
               prog_main P1 = prog_main P2 -> 

               (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
               GenvHyp P1 P2 ->

                I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 -> 
               compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 |  cc_inj : forall  (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
               entrypoints jInit
               (Inj_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_vars)->
                     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_vars)
                                        /\ Mem.inject jInit m1 m2))
               (ePts_ok: entryPts_inject_ok P1 P2 jInit ExternIdents entrypoints)
               (preserves_globals: meminj_preserves_globals (Genv.globalenv P1) jInit)
               (R:Sim_inj.Forward_simulation_inject _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints), 
               prog_main P1 = prog_main P2 ->

               (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
               GenvHyp P1 P2 ->
                externvars_ok P1 ExternIdents ->

                I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 -> 
               compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 | cc_trans: forall  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (Sem3 : CompcertCoreSem (Genv.t F3 V3) C3 (list (ident * globvar V3)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
               (P3 : AST.program F3 V3),
                 compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
                 compiler_correctness I ExternIdents F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3 ->
                 compiler_correctness I ExternIdents F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
 
Lemma cc_I: forall {F1 C1 V1 F2 C2 V2}
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)  ExternIdents I,
                    compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
                     I _ _ _ Sem1 P1 /\ I _ _ _ Sem2 P2.
   Proof. intros. induction X; intuition. Qed.

Lemma cc_main: forall {F1 C1 V1 F2 C2 V2}
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)  ExternIdents I,
                    compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
                    prog_main P1 = prog_main P2.
   Proof. intros. induction X; intuition. congruence. Qed.

(*TRANSITIVITY OF THE GENV-ASSUMPTIONS:*)
Lemma cc_Genv:forall {F1 C1 V1 F2 C2 V2}
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2 (list (ident * globvar V2)))
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)  ExternIdents I,
                    compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
               GenvHyp P1 P2.
   Proof. intros. induction X; intuition. 
       destruct IHX1.
       destruct IHX2.
        split; intros; eauto. rewrite H1. apply H. Qed.
End CompilerCorrectness.

    