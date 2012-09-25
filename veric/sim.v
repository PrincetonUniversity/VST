Add LoadPath "..".
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
Record CoreSemantics {G C M:Type} : Type :=
  { initial_mem: G -> M -> Prop (*characterizes initial memories*)
  ; make_initial_core : G -> val -> list val -> option C
  ; at_external : C -> option (external_function * list val)
  ; after_external : val -> C -> option C
  ; safely_halted : G -> C -> option int (*maybe delete this, too?*)
  ; corestep : G -> C -> M -> C -> M -> Prop

  ; corestep_not_at_external:
       forall ge m q m' q', corestep ge q m q' m' -> at_external q = None

  ; corestep_not_halted :
       forall ge m q m' q', corestep ge q m q' m' -> safely_halted ge q = None

  ; at_external_halted_excl :
       forall ge q, at_external q = None \/ safely_halted ge q = None
  }.
Implicit Arguments CoreSemantics [].

(* Definition of multistepping. *)
Section corestepN.
  Context {G C M E:Type} (Sem:CoreSemantics G C M) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
    | O => fun c m c' m' => (c,m) = (c',m')
    | S n => fun c1 m1 c3 m3 => exists c2, exists m2,
               corestep Sem ge c1 m1 c2 m2 /\
               corestepN n c2 m2 c3 m3
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
Record CompcertCoreSem {G C} :=
{ csem :> CoreSemantics G C mem

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


Lemma corestepN_fun (G C:Type) (CSem:CompcertCoreSem G C) :
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

Inductive entry_points_compose: list (val*val*signature) -> list (val*val*signature) -> list (val*val*signature) -> Prop :=
| EPC1: forall v1 v2 v3 sig r1 r2 r3, 
                   entry_points_compose r1 r2 r3 ->
                   entry_points_compose ((v1,v2,sig)::r1) ((v2,v3,sig)::r2) ((v1,v3,sig)::r3)
| EPC0: entry_points_compose nil nil nil.

 
(* Here we present a module type which expresses the sort of forward simulation
   lemmas we have avalaible.  The idea is that these lemmas would be used in
   the individual compiler passes and the composition lemma would be used
   to build the main lemma.
 *)
Module Type SIMULATIONS.

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
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

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
      forall d st1 st2 e args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,args) ->
        ( at_external Sem2 st2 = Some (e,args) /\
          Forall2 Val.has_type args (sig_args (ef_sig e)) );

    core_after_external :
      forall d st1 st2 ret e args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,args) ->
        at_external Sem2 st2 = Some (e,args) ->
        Forall2 Val.has_type args (sig_args (ef_sig e)) ->
        Val.has_type ret (proj_sig_res (ef_sig e)) ->
        exists st1', exists st2', exists d',
          after_external Sem1 ret st1 = Some st1' /\
          after_external Sem2 ret st2 = Some st2' /\
          match_core d' st1' st2'
  }.
End Forward_simulation_equals. 

Implicit Arguments Forward_simulation_equals [[G1] [C1] [G2] [C2]].
End Sim_eq.

Module Sim_ext.

(* Next, an axiom for passes that allow the memory to undergo extension. *)
Section Forward_simulation_extends. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

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
      forall cd st1 m1 st2 m2 e vals1,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' -> (*ie spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists st1', exists st2', exists cd',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'
   }.
End Forward_simulation_extends.

Implicit Arguments Forward_simulation_extends [[G1] [C1] [G2] [C2]].
End Sim_ext.

Module Sim_inj.
(* An axiom for passes that use memory injections. *)
Section Forward_simulation_inject. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
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
(*
    core_at_externalLenbAteempt : 
      forall cd js st1 m1 st2 m2 e vals1,
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        (Mem.inject (injlist_compose js) m1 m2 /\
          exists vals2, Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2));
*)
    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        ( Mem.inject j m1 m2 /\
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2));
  (*
    (core_after_externalForwardSimulation.v :
      forall cd j j' st1 st2 m1 m2 e1 e2 vals vals' ret ret' m1' m2' sig,
        match_state cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        at_external Sem2 st2 = Some (e2,sig,vals') ->
        match_ext sig e1 e2 ->
        Forall2 (val_inject j) vals vals' ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret ret' ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals' (sig_args sig) ->
        Val.has_type ret' (proj_sig_res sig) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret'::nil) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'),*)

    core_after_external :
      forall cd j j' st1 st2 m1 e vals1 (*vals2*) ret1 m1' m2 m2' ret2,
        Mem.inject j m1 m2->
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
(*        Mem.inject j m1 m2 ->
        at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->*)
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         mem_unchanged_on (loc_unmapped j) m1 m1' ->
         mem_forward m2 m2' -> 
         mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
         Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'
    }.

End Forward_simulation_inject. 

Implicit Arguments Forward_simulation_inject [[G1] [C1] [G2] [C2]].
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

Module CompilerCorrectness.

Definition globvar_eq {V1 V2: Type} (v1:globvar V1) (v2:globvar V2) :=
    match v1, v2 with mkglobvar _ init1 readonly1 volatile1, mkglobvar _ init2 readonly2 volatile2 =>
                        init1 = init2 /\ readonly1 =  readonly2 /\ volatile1 = volatile2
   end.

Inductive external_description :=
   extern_func: signature -> external_description
| extern_globvar : external_description.

Definition entries_ok  {F1 V1 F2 V2:Type}  (P1 : AST.program F1 V1)    (P2 : AST.program F2 V2) 
                                       (ExternIdents : list (ident * external_description)) (entries: list (val * val * signature)): Prop :=
          forall e d, In (e,d) ExternIdents ->
                              exists b, Genv.find_symbol  (Genv.globalenv P1) e = Some b /\
                                             Genv.find_symbol (Genv.globalenv P2) e = Some b /\
                                             match d with
                                                      extern_func sig => In (Vptr b Int.zero,Vptr b Int.zero, sig) entries /\
                                                                                     exists f1, exists f2, Genv.find_funct_ptr (Genv.globalenv P1) b = Some f1 /\ 
                                                                                                                      Genv.find_funct_ptr (Genv.globalenv P2) b = Some f2
                                                    | extern_globvar  => exists v1, exists v2, Genv.find_var_info  (Genv.globalenv P1) b = Some v1 /\
                                                                                                                    Genv.find_var_info  (Genv.globalenv P2) b = Some v2 /\
                                                                                                                    globvar_eq v1 v2
                                             end.

Definition entries_inject_ok  {F1 V1 F2 V2:Type}  (P1 : AST.program F1 V1)    (P2 : AST.program F2 V2)  (j: meminj)
                                       (ExternIdents : list (ident * external_description)) (entries: list (val * val * signature)): Prop :=
          forall e d, In (e,d) ExternIdents ->
                              exists b1, exists b2, Genv.find_symbol (Genv.globalenv P1) e = Some b1 /\
                                                                Genv.find_symbol (Genv.globalenv P2) e = Some b2 /\
                                                                j b1 = Some(b2,0) /\
                                             match d with
                                                      extern_func sig => In (Vptr b1 Int.zero,Vptr b2 Int.zero, sig) entries /\
                                                                                     exists f1, exists f2, Genv.find_funct_ptr (Genv.globalenv P1) b1 = Some f1 /\ 
                                                                                                                      Genv.find_funct_ptr (Genv.globalenv P2) b2 = Some f2
                                                    | extern_globvar  => exists v1, exists v2, Genv.find_var_info  (Genv.globalenv P1) b1 = Some v1 /\
                                                                                                                    Genv.find_var_info  (Genv.globalenv P2) b2 = Some v2 /\
                                                                                                                    globvar_eq v1 v2
                                             end.

Inductive compiler_correctness (I: forall F C V  (Sem : CompcertCoreSem (Genv.t F V) C)  (P : AST.program F V),Prop)
        (ExternIdents: list (ident * external_description)):
       forall (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2), Type :=
   cc_eq : forall  (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
 (*              (match_prog:  precise_match_program F1 F2 V1 V2 P1 P2)*)
               (Eq_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 ->
                     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 
                                        /\ m1 = m2))
               entrypoints
               (ext_ok: entries_ok P1 P2 ExternIdents entrypoints)
               (R:Sim_eq.Forward_simulation_equals Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints), 
               prog_main P1 = prog_main P2 -> 
                I _ _ _  Sem1 P1 -> I _ _ _  Sem2 P2 -> 
               compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 |  cc_ext : forall  (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
(*               (match_prog:  precise_match_program F1 F2 V1 V2 P1 P2)*)
               (Extends_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 ->
                     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 
                                        /\ Mem.extends m1 m2))
               entrypoints
               (ext_ok: entries_ok P1 P2 ExternIdents entrypoints)
               (R:Sim_ext.Forward_simulation_extends Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
               prog_main P1 = prog_main P2 -> 
                I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 -> 
               compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 |  cc_inj : forall  (F1 C1 V1 F2 C2 V2:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
               entrypoints j
               (Inj_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 ->
                     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 
                                        /\ Mem.inject j m1 m2))
               (ext_ok: entries_inject_ok P1 P2 j ExternIdents entrypoints)
               (R:Sim_inj.Forward_simulation_inject Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints), 
               prog_main P1 = prog_main P2 ->
                I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 -> 
               compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 | cc_trans: forall  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (Sem3 : CompcertCoreSem (Genv.t F3 V3) C3)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)
               (P3 : AST.program F3 V3),
                 compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
                 compiler_correctness I ExternIdents F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3 ->
                 compiler_correctness I ExternIdents F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
 
Lemma cc_I: forall {F1 C1 V1 F2 C2 V2}
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)  ExternIdents I,
                    compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
                     I _ _ _ Sem1 P1 /\ I _ _ _ Sem2 P2.
   Proof. intros. induction X; intuition. Qed.

Lemma cc_main: forall {F1 C1 V1 F2 C2 V2}
               (Sem1 : CompcertCoreSem (Genv.t F1 V1) C1)
               (Sem2 : CompcertCoreSem (Genv.t F2 V2) C2)
               (P1 : AST.program F1 V1)
               (P2 : AST.program F2 V2)  ExternIdents I,
                    compiler_correctness I ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
                    prog_main P1 = prog_main P2.
   Proof. intros. induction X; intuition. congruence. Qed.

End CompilerCorrectness.

Require Import compcert.Smallstep.

Module Type COMPILER_CORRECTNESS_COMPCERT_SIM.

  Section CoreSem_to_semantics.
    Variables (F C V:Type).
    Let genv  := Genv.t F V.
    Variable (Sem:CompcertCoreSem genv C).

    Let state := (C * mem)%type.

    Inductive step (ge:genv) : state -> trace -> state -> Prop :=
    | step_corestep : forall c m c' m',
          corestep Sem ge c m c' m' ->
          step ge (c,m) E0 (c',m')

    | step_ext_step : forall c m c' m' ef args tr ret,
          at_external Sem c = Some (ef,args) ->
          external_call ef ge args m tr ret m' ->
          after_external Sem ret c = Some c' ->
          step ge (c,m) tr (c',m').

    Variable (prog:AST.program F V).

    (*Definition main_sig : signature := 
       mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint).*)
    Definition main_sig : signature := 
       mksignature (nil) (Some AST.Tint).

    Definition initial_state (st:state) : Prop :=
      exists b, exists vals,
        Forall2 (val_inject (Mem.flat_inj (Mem.nextblock (snd st)))) vals vals /\
        Forall2 Val.has_type vals (sig_args main_sig) /\
        Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
        make_initial_core Sem (Genv.globalenv prog) (Vptr b Int.zero) vals = Some (fst st) /\
        Genv.init_mem prog = Some (snd st). 

    Definition final_state (st:state) (i:int) : Prop :=
      safely_halted Sem (Genv.globalenv prog) (fst st) = Some i.

   Definition mk_semantics: semantics :=
           Semantics  step initial_state final_state (Genv.globalenv prog).
  End CoreSem_to_semantics.
Check mk_semantics. 

Lemma corestep_plus_step: forall F C V (Sem:CompcertCoreSem (Genv.t F V) C) P c m c' m',
         corestep Sem (Genv.globalenv P) c m c' m' ->
         plus (step F C V Sem) (Genv.globalenv P) (c, m) E0 (c', m').
  Proof. intros.  eapply plus_left. eapply step_corestep. apply H.  apply star_refl. rewrite E0_left. trivial. Qed.

Lemma corestep_plus_plus_step: forall F C V (Sem:CompcertCoreSem (Genv.t F V) C) P c m c' m',
              corestep_plus Sem (Genv.globalenv P) c m c' m' -> plus (step F C V Sem) (Genv.globalenv P) (c, m) E0 (c', m').
  Proof. intros. unfold corestep_plus in H. destruct H as [n Hn].
      generalize dependent m.  generalize dependent c. 
      induction n.
         simpl; intros. destruct Hn as [c2 [m2 [Hstep X]]]. inv X. eapply corestep_plus_step; auto.
      intros. simpl in Hn. destruct Hn as [c1 [m1 [Hstep X]]].
          eapply plus_left. eapply step_corestep. apply Hstep.
             eapply plus_star. eapply IHn. apply X.  rewrite E0_left. trivial.
  Qed.

Lemma corestep_star_star_step: forall F C V (Sem:CompcertCoreSem (Genv.t F V) C) P c m c' m',
              corestep_star Sem (Genv.globalenv P) c m c' m' -> star (step F C V Sem) (Genv.globalenv P) (c, m) E0 (c', m').
  Proof. intros. unfold corestep_star in H. destruct H as [n Hn].
      destruct n; simpl in Hn. inv Hn. apply star_refl. 
      eapply plus_star. eapply corestep_plus_plus_step. exists n. apply Hn.
  Qed.

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

(*Axioms ExtAX: forall args m t r m', external_call ef (Genv.globalenv P1) args m t r m1 -> In ef ExternIdents)*)

Theorem CompilerCorrectness_implies_CompcertForwardSimulation:
     forall F1 C1 V1 F2 C2 V2
        (Sem1: CompcertCoreSem (Genv.t F1 V1) C1)  
        (Sem2: CompcertCoreSem (Genv.t F2 V2) C2)
        P1 P2 ExternIdents,
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> P1.(prog_main) = P2.(prog_main) ->
        CompilerCorrectness.compiler_correctness
             (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <-> initial_mem Sem (Genv.globalenv P) x) /\
                                                  (forall ef myF args m t r m', external_call ef (Genv.globalenv P) args m t r m' -> In myF ExternIdents))
              ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
        forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2).
Proof.
  intros.
  induction X; intros.
  Focus 4. (*trans_case*)
     assert (MM: prog_main P1 = prog_main P2). eapply CompilerCorrectness.cc_main; eauto.
      spec IHX1.  apply H.
      spec IHX1. apply MM.  
      spec IHX2. rewrite MM in H. apply H.
      spec IHX2. eapply CompilerCorrectness.cc_main; eauto.
      clear X1 X2.
      eapply compose_forward_simulation; eauto.
  (*equals_case*)
        intros.
        set (fsim_index := Sim_eq.core_data R).
        set (fsim_order := Sim_eq.core_ord R).
        set (fsim_order_wf := Sim_eq.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                          Sim_eq.match_core R s (fst x) (fst y) /\ snd x = snd y).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1].
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       unfold CompilerCorrectness.entries_ok in ext_ok.
                       destruct (ext_ok _ _ H) as [bb [KK1 [KK2 [KK3 KK4]]]].
                      assert (X := @Sim_eq.core_initial _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ KK3 nil).
                      simpl in X.  destruct X. constructor. 
                            destruct H1 as [cc1 [cc2 [ini1 [ini2 mtch]]]].
                          exists x. exists (cc2,m1).
                         split. simpl. exists bb. exists nil. simpl.
                             repeat  split; try constructor. rewrite <- H0. apply KK2.
                                assumption.
                           destruct (Eq_init m1).  apply i. apply K5. destruct H1; subst. simpl in *. apply i0. apply H1. 
                      simpl. hnf. simpl in *. split; trivial. rewrite K3 in KK1. inv KK1.  inv K2. rewrite K4 in ini1.  inv ini1. assumption.
           (*finalstate*)
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      destruct H1. simpl in H3. subst.  simpl in *.
                      apply (@Sim_eq.core_halted _ _ _ _ Sem1 Sem2
                                    (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ H1 H2).
           (*diagram*)
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                      destruct H2. subst.
                 inv H1.
                 (*corestep*)  
                   assert (DD := @Sim_eq.core_diagram _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ H2).
                   destruct DD as [c2' [d' [MC myStep]]].
                  exists d'. exists (c2', m1'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_eq.core_at_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ H2 H8) as [AtExt2 TP].
                    assert (DD := @Sim_eq.core_after_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H9).
                    destruct (DD _ _ _ ret _ _ H2 H8 AtExt2 TP RetTp) as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
                    rewrite AftExt1 in H10. inv H10.
                    exists d'. exists (c2', m1'). simpl.
                    split; auto. left.  eapply plus_one. eapply step_ext_step. apply AtExt2. Focus 2. apply AftExt2.
                                  eapply external_call_symbols_preserved_gen. Focus 3. apply H9. admit. (*HERE*)
                              (*globvar*) intros. unfold block_is_volatile. 
                                      remember  (Genv.find_var_info (Genv.globalenv P1) b) as v.
                                      destruct v; apply eq_sym in Heqv.
                                         admit. (*don't have b in extenidents, so can't apply ext_ok*)
                                      admit. (*our gvar assumptions are assymmetric*)
         (* fsim_symbols_preserved*) simpl. admit. (*SAME HERE*)
   (*extends*) 
        destruct i as [GenvInit1 HGenv1].
        destruct i0 as [GenvInit2 HGenv2].
        set (fsim_index := Sim_ext.core_data R).
        set (fsim_order := Sim_ext.core_ord R).
        set (fsim_order_wf := Sim_ext.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        Sim_ext.match_state R s (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       unfold CompilerCorrectness.entries_ok in ext_ok.
                       destruct (ext_ok _ _ H) as [b1 [KK1 [KK2 [Hfound [f1 [f2 [Hf1 Hf2]]]]]]].
                       rewrite KK1 in K3. inv K3. inv K2. clear K1 ext_ok H.
                       apply GenvInit1 in K5. apply Extends_init in K5. destruct K5 as [m2 [iniMem2 Mextends]].
                      assert (X := @Sim_ext.core_initial _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil nil m1 m2).
                      destruct X as [d' [c1' [c2' [IniCore1 [IniCore2 ExtMatch]]]]].
                          constructor.
                          constructor.
                          assumption.
                    rewrite IniCore1 in K4. inv K4.
                    exists d'. exists (c2', m2); simpl. 
                         split; auto. 
                          exists b. exists nil. simpl.
                          repeat  split; try constructor. 
                          rewrite <- H0. apply KK2.  
                         assumption.
                         apply GenvInit2. apply iniMem2. 
           (*finalstate*)
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      eapply (@Sim_ext.core_halted _ _ _ _ Sem1 Sem2
                                    (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ _ _ _ H2).
           (*diagram*)
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_ext.core_diagram _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ _ H2).
                   destruct DD as [c2' [m2' [d'  [MC' myStep]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_ext.core_at_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ H2 H8) as [args2 [Mextends [lessArgs [TpArgs2 AtExt2]]]].
                   assert (EXT:= @external_call_mem_extends _ _ _ _ _ _ _ _ _  _ _ H9 Mextends (forall_lessdef_val_listless _ _ lessArgs)).
                   destruct EXT as [ret2 [m2' [extCall2 [lessRet [Mextends' MunchOn]]]]].
                    assert (DD := @Sim_ext.core_after_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ ret ret2 m1' m2' H2 H8 AtExt2 lessArgs TpArgs2).
                    destruct DD as [c1'' [c2' [d' [AftExt1 [AftExt2 Match']]]]].
                            admit.
                            admit.
                            assumption.
                            assumption.
                            assumption.
                            apply (external_call_well_typed _ _ _ _ _ _ _ extCall2). 
                    rewrite AftExt1 in H10. inv H10.
                      exists d'. exists (c2', m2'); simpl.
                     split; auto. left.  eapply plus_one.
                               apply step_ext_step with (ef:=ef)(args:=args2)(ret:=ret2).
                                    apply AtExt2. 
                                    apply (@external_call_symbols_preserved_2 ef F1 V1 F2 V2 (fun v1 =>Errors.Error nil)) with (ge1:=(Genv.globalenv P1)).
                                          apply extCall2.
                                          admit. (*symmetric hypothesis on Genv.findSymbol*) 
                                          simpl. admit. (*first hyp on globvars*) 
                                          simpl. admit. (*second hyp on globvars*) 
                                    assumption.
         (* fsim_symbols_preserved*) simpl. admit. (*SAME HERE*)
   (*inject*)
        rename j into jInit. rename i into HGenv1. rename i0 into HGenv2.
        set (fsim_index := Sim_inj.core_data R).
        set (fsim_order := Sim_inj.core_ord R).
        set (fsim_order_wf := Sim_inj.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        exists j,  inject_incr jInit j /\  Sim_inj.match_state R s j (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       unfold CompilerCorrectness.entries_ok in ext_ok.
                       destruct (ext_ok _ _ H) as [b1 [b2 [KK1 [KK2 [Hjb [Hfound [f1 [f2 [Hf1 Hf2]]]]]]]]].
                      rewrite KK1 in K3. inv K3. inv K2. clear K1.
                       destruct (Inj_init m1) as [m2 [initMem2 Inj]]; clear Inj_init . apply HGenv1. apply K5.
                        assert (X := @Sim_inj.core_initial _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil _ _ _ nil _ K4 Inj).
                        (*would need relationship between entrypoints and externidents assert (ZZ: (forall (w1 w2 : val) (sigg : signature),  In (w1,w2, sigg) entrypoints -> val_inject j w1 w2)).
                             intros.  unfold CompilerCorrectness.entries_inject_ok in ext_ok. apply ext_ok in H1.*)
                        destruct X as [d' [c2 [iniCore2 Match]]].
                          constructor.
                          constructor. 
                          exists d'. exists (c2,m2). simpl in *.
                          split; auto. exists b2. exists nil.
                             repeat  split; try constructor.
                             rewrite <- H0. apply KK2.
                             assumption.
                             apply HGenv2. apply initMem2.
                         exists jInit. split; auto. 
           (*finalstate*)
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      eapply (@Sim_inj.core_halted _ _ _ _ Sem1 Sem2
                                    (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ _ _ _ _ H2).
           (*diagram*) 
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                destruct H2 as [j [InjJ MCJ]].
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_inj.core_diagram _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H5 _ _ _ _ MCJ).
                   destruct DD as [c2' [m2' [d' [j' [InjJ' [Sep [MC' myStep]]]]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
                   exists j'; split; auto. eapply inject_incr_trans. apply InjJ. apply InjJ'.                    
               (*external_step*) 
                    destruct (@Sim_inj.core_at_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ MCJ H7) 
                               as[INJ [args2 [LD [TP AtExt2]]]].
                    assert (HH: meminj_preserves_globals (Genv.globalenv P1) j). it seems inject doesn't preserve globals!
                             split; intros. destruct HGenv1. apply (H3 _ (id, CompilerCorrectness.extern_func (ef_sig ef))) in H8.  apply ext_ok in H8.
                                    destruct H8 as [b1 [b2 [Hb1 [Hb2 [Hb1b2 _]]]]]. rewrite Hb1 in H1. inv H1.  apply InjJ. assumption.
                    apply forall_inject_val_list_inject in LD.
                   assert (ZZ:= @external_call_mem_inject ef  _ _ (Genv.globalenv P2) _ _ _ _ _ j _ _ HH H8 INJ LD).
                   destruct ZZ as [j'  [ret2 [m2' [ExtCall2 [RetInj [MInj2 [Munch1 [Munch2 [Inj' Sep']]]]]]]]].
                     assert (DD := @Sim_inj.core_after_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R i j j').
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H8).
                    destruct (DD _ _ _ _ _ _ _ _ _ _ INJ MCJ H7 Inj' Sep' MInj2 RetInj) as [d' [c1'' [c2' [AftExt1 [AftExt2 Match2]]]]]; clear DD.
                         admit. (*mem_forward*)
                         apply Munch1.
                         admit. (*mem_forward*)
                         apply Munch2.
                         eapply external_call_well_typed. apply ExtCall2. 
                      rewrite AftExt1 in H9. inv H9.
                         exists d'. exists (c2', m2').
                         split. left. apply plus_one. eapply  step_ext_step. apply AtExt2. rewrite apply ExtCall2. 
                         apply inject_incr_refl. intros z. intros. rewrite H1 in H2. inv H2.   apply inject_separated_refl.  AtExt2 LD TP) as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
                       admit. (*apply mem_forward_refl.*)
                       admit. (*apply mem_forward_refl.*)
                       admit. (*apply mem_forward_refl.*)
                      apply Val.lessdef_refl.
                      apply Xt.
                      apply RetTp.
                    rewrite AftExt1 in H10. inv H10.
                    exists d'. exists (c2', m2). simpl.
                    split; auto. left.  eapply plus_one. eapply step_ext_step. apply AtExt2. Focus 2. apply AftExt2.
                                  eapply external_call_symbols_preserved_gen. Focus 3. apply H9. admit. (*HERE*)
                                      admit. (*property about volatile*)
         (* fsim_symbols_preserved*) simpl. admit. (*SAME HERE*)
   (*extends*)
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        exists j',  inject_incr j j' /\  Sim_inj.match_state R s j' (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       unfold CompilerCorrectness.entries_ok in ext_ok.
                       destruct (ext_ok _ _ H) as [b1 [b2 [KK1 [KK2 [Hjb [Hfound [f1 [f2 [Hf1 Hf2]]]]]]]]].
                      rewrite KK1 in K3. inv K3. inv K2. clear K1.
                       destruct (Inj_init m1) as [m2 [initMem2 Inj]]; clear Inj_init . apply i. apply K5.
                        assert (X := @Sim_inj.core_initial _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil _ _ _ nil _ K4 Inj).
                        (*would need relationship between entrypoints and externidents assert (ZZ: (forall (w1 w2 : val) (sigg : signature),  In (w1,w2, sigg) entrypoints -> val_inject j w1 w2)).
                             intros.  unfold CompilerCorrectness.entries_inject_ok in ext_ok. apply ext_ok in H1.*)
                        destruct X as [d' [c2 [iniCore2 Match]]].
                          constructor.
                          constructor. 
                          exists d'. exists (c2,m2). simpl in *.
                          split; auto. exists b2. exists nil.
                             repeat  split; try constructor.
                             rewrite <- H0. apply KK2.
                             assumption.
                             apply i0. apply initMem2.
                         exists j. split; auto. 
           (*finalstate*)
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      eapply (@Sim_inj.core_halted _ _ _ _ Sem1 Sem2
                                    (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ _ _ _ _ H2).
           (*diagram*)
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                destruct H2 as [j' [Inj MC]].
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_inj.core_diagram _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H5 _ _ _ _ MC).
                   destruct DD as [c2' [m2' [d' [j'' [Inj' [Sep [MC' myStep]]]]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
                   exists j''; split; auto. eapply inject_incr_trans. apply Inj. apply Inj'.                    
               (*external_step*) 
                    destruct (@Sim_inj.core_at_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ MC H7) as[INJ [arg2 [LD [TP AtExt2]]]].
                    assert (DD := @Sim_inj.core_after_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H8).
                    destruct (DD _ _ _ _ _ _ _ _ ret ret m1' m2 H2 H8 AtExt2 LD TP) as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
                       admit. (*apply mem_forward_refl.*)
                       admit. (*apply mem_forward_refl.*)
                       admit. (*apply mem_forward_refl.*)
                      apply Val.lessdef_refl.
                      apply Xt.
                      apply RetTp.
                    rewrite AftExt1 in H10. inv H10.
                    exists d'. exists (c2', m2). simpl.
                    split; auto. left.  eapply plus_one. eapply step_ext_step. apply AtExt2. Focus 2. apply AftExt2.
                                  eapply external_call_symbols_preserved_gen. Focus 3. apply H9. admit. (*HERE*)
                                      admit. (*property about volatile*)
         (* fsim_symbols_preserved*) simpl. admit. (*SAME HERE*)
   (*extends*)

   (*extends*)
        intros.
        set (fsim_index := Sim_ext.core_data R).
        set (fsim_order := Sim_ext.core_ord R).
        set (fsim_order_wf := Sim_ext.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                          Sim_ext.match_state R s (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       unfold CompilerCorrectness.entries_ok in ext_ok.
                       destruct (ext_ok _ _ H) as [bb [KK1 [KK2 [KK3 [f1 [f2 [Hf1 Hf2]]]]]]].
                       assert (X := @Sim_ext.core_initial _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ KK3 nil nil).
                       rewrite KK1 in K3. inv K3. inv K2. clear K1.  
                       simpl in *.
                       destruct (Extends_init m1) as [m2 [initMem2 Y]].  apply i. apply K5.
                      destruct (X m1 m2); clear X.
                          constructor. 
                          constructor. 
                          apply Y.
                          destruct H1 as [cc1 [c2 [iniCore1 [iniCore2 mtch]]]]. rewrite iniCore1 in K4. inv K4.
                          exists x. exists (c2,m2). simpl in *.
                          split; auto. exists b. exists nil.
                             repeat  split; try constructor.
                             rewrite <- H0. apply KK2.
                             assumption.
                             apply i0. apply initMem2. 
           (*finalstate*)
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      eapply (@Sim_ext.core_halted _ _ _ _ Sem1 Sem2
                                    (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ _ _ H1 H2).
           (*diagram*)
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                 inv H1.
                 (*corestep*)  
                   assert (DD := @Sim_ext.core_diagram _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ _ H2).
                   destruct DD as [c2' [m2' [d' [MC myStep]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_ext.core_at_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ H2 H8) as [arg2 [Xt [LD [TP AtExt2]]]].
                    assert (DD := @Sim_ext.core_after_external _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H9).
                    destruct (DD _ _ _ _ _ _ _ _ ret ret m1' m2 H2 H8 AtExt2 LD TP) as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
                       admit. (*apply mem_forward_refl.*)
                       admit. (*apply mem_forward_refl.*)
                       admit. (*apply mem_forward_refl.*)
                      apply Val.lessdef_refl.
                      apply Xt.
                      apply RetTp.
                    rewrite AftExt1 in H10. inv H10.
                    exists d'. exists (c2', m2). simpl.
                    split; auto. left.  eapply plus_one. eapply step_ext_step. apply AtExt2. Focus 2. apply AftExt2.
                                  eapply external_call_symbols_preserved_gen. Focus 3. apply H9. admit. (*HERE*)
                                      admit. (*property about volatile*)
         (* fsim_symbols_preserved*) simpl. admit. (*SAME HERE*)
   (*extends*)


Qed.

Old material

Definition siminj (j: meminj) (m1 m2 : mem) :=
  (forall b, ~(Mem.valid_block m1 b) -> j b = None) /\
  (forall b b' delta, j b = Some(b', delta) -> Mem.valid_block m2 b').

Fixpoint injlist_compose (j : list meminj) : meminj :=
  match j with 
     nil => fun b => Some (b,0)
  | cons h t => Mem.meminj_compose h (injlist_compose t)
  end.

Fixpoint check_injectlist (js : list meminj) m1 ms lst : Prop :=
   match js,ms with
     nil, nil => m1 = lst
   | cons j J, cons m M => Mem.inject j m1 m /\ check_injectlist J m M lst
   | _ , _ => False
   end.

Fixpoint check_returns (js : list meminj) ret1 (rets : list val) r : Prop :=
  match js, rets with 
     nil, nil => r=ret1
  | (j::J), (ret2::R) => val_inject j ret1 ret2 /\ check_returns J ret2 R r
  | _ , _ => False
  end.

Fixpoint check_valslist (js : list meminj) (vals1 : list val) (vals:list (list val)) (w: list val): Prop :=
   match js,vals with
     nil, nil => vals1 = w 
   | cons j J, cons vals2 V => 
          Forall2 (val_inject j) vals1 vals2 /\ check_valslist J vals2 V w
   | _ , _ => False
   end.

Fixpoint mem_square js m1 ms m1' ms' : Prop :=
  match js, ms, ms' with
    nil, nil , nil => mem_forward m1 m1' 
 |  j::jss, m2::mss, m2'::mss' => mem_unchanged_on (loc_unmapped j) m1 m1' /\
                                 mem_unchanged_on (loc_out_of_reach j m1) m2 m2' /\
                                 mem_forward m1 m1' /\ mem_square jss m2 mss m2' mss'
 | _ , _ , _ => False
  end.

Fixpoint mkInjections m (n:nat) : list meminj :=
  match n with O => nil
            | S n' => (Mem.flat_inj (Mem.nextblock m))::mkInjections m n'
  end.

Fixpoint lift_join (join:mem -> mem -> mem -> Prop) ms1 ms2 ms :=
  match ms1,ms2,ms with 
     nil, nil, nil => True
   | h1::t1,h2::t2,h::t => join h1 h2 h /\ lift_join join t1 t2 t
   | _ , _ , _ => False
  end.

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop)
            : list A -> list B -> list C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil
  | Forall3_cons : forall (x : A) (y : B) (z:C) (l : list A) (l' : list B) (l'' : list C),
                   R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z::l'').

  
  Record Forward_simulation_inject_onepass := {
    core_dataOP : Type;

    match_stateOP : core_dataOP -> meminj -> C1 -> mem -> C2 -> mem -> Prop;
    core_ordOP : core_dataOP -> core_dataOP -> Prop;
    core_ord_wfOP : well_founded core_ordOP;

(*Maybe we need an axiom like this?
    thread_axiom: forall cd j m1 c1 m2 c2, match_state cd j c1 m1 c2 m2 ->
             (*we want maybe same sequence of memops to be applied in both forward_modifications*)
               allowed_forward_modifications m1 m1' ->
               allowed_forward_modifications m2 m2' ->
           exists j', incject_incr j j' /\ inject_separated j j' m1 m2
               match_state cd j' c1 m1' c2 m2';
*)

    match_state_siminjOP :
      forall cd j st1 m1 st2 m2,
        match_stateOP cd j st1 m1 st2 m2 -> siminj j m1 m2;

    core_diagramOP : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_stateOP cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_stateOP cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ordOP cd' cd);

    core_initialOP : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          let j := (Mem.flat_inj (Mem.nextblock m1)) in

           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->

          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_stateOP cd j c1 m1 c2 m2;

(* Attempt to specify forking, but we're giving away the entire memory here which can't be right.
  We may later want to reintroduce this lemma, but somehow allow one to specify which part of
the memory is retained, and which one is given to the thread.
    core_at_fork : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2 j
          (HM: match_state cd j c1 m1 c2 m2),

           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           (*Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           Forall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->*)

          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd', exists c1', exists c2',
            make_initial_core Sem1 ge1 v1 vals = Some c1' /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2' /\
            match_state cd' j c1' m1 c2' m2;*)

    core_haltedOP : forall cd j c1 m1 c2 m2 (v1:int),
      match_stateOP cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         Mem.inject j m1 m2); (*conjunct Mem.inject j m1 m2 could maybe deleted here?*)

    core_at_externalOP: 
      forall cd j st1 m1 st2 m2 e vals1,
        match_stateOP cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.inject j m1 m2 /\
          Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);
  
    core_after_externalOP :
      forall cd j j' st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_stateOP cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->  (*together, these 2 conditions say roughly that*)
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' -> (* spill-locations didn't change*)

        mem_forward m1 m1' ->  
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) ->
        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_stateOP cd' j' st1' m1' st2' m2'
    }.

  Axiom OnePassSpecialization: Forward_simulation_inject_onepass -> Forward_simulation_inject.

End Forward_simulation_inject.

Implicit Arguments Forward_simulation_inject[[G1] [C1] [G2] [C2]].
End Sim_inj.

  (* An axiom stating that inject forward simulations compose *)
  Axiom forward_simulation_inject_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : Sim_inj.Forward_simulation_inject Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.

  (* An axiom stating that extend_inject forward simulations compose *)
  Axiom forward_simulation_extend_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : Sim_ext.Forward_simulation_extends Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.

  (* An axiom stating that equal inject forward simulations compose *)
  Axiom forward_simulation_equal_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : Sim_eq.Forward_simulation_equals Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : Sim_inj.Forward_simulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    Sim_inj.Forward_simulation_inject Sem1 Sem3 ge1 ge3 entry_points13.

End SIMULATIONS.

(* This module type states that forward simulations are sufficent
   to imply correctness with respect to the trace model of external
   functions.  First we demonstrate how to hook up an arbitrary
   EXtSem with the trace model, then we show simulation in the
   forward and backward direction.  Finally we show that
   the compiler preserves all trace behaviors for safe input
   programs.
 *)

(* COMMENTED OUT by Andrew, until Rob can adjust it to CompCert's new-style
    "semantics" definition 

Require Import compcert.Smallstep.
Require Import compcert.Determinism.
Require Import compcert.Behaviors.

Module Type TRACE_CORRECTNESS.

  Section EXtSem_to_trace.
    Variables (F C V:Type).
    Variable (Sem:CompcertCoreSem F C V external_function).

    Let genv  := G.
    Let state := (C * mem)%type.

    Inductive step (ge:genv) : state -> trace -> state -> Prop :=
    | step_corestep : forall c m c' m',
          corestep Sem ge c m c' m' ->
          step ge (c,m) E0 (c',m')

    | step_ext_step : forall c m c' m' ef sig args tr ret,
          at_external Sem c = Some (ef,sig,args) ->
          sig = ef_sig ef ->
          external_call ef ge args m tr ret m' ->
          after_external Sem (ret::nil) c = Some c' ->
          step ge (c,m) tr (c',m').

    Variable (prog:program (fundef F) V).

    Definition main_sig : signature := 
      mksignature (Tint :: Tint :: nil) (Some Tint).

    Definition initial_state (st:state) : Prop :=
      exists b, exists vals,
        Forall2 (val_inject (Mem.flat_inj (Mem.nextblock (snd st)))) vals vals /\
        Forall2 Val.has_type vals (sig_args main_sig) /\
        Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
        make_initial_core Sem (Genv.globalenv prog) (Vptr b Int.zero) vals = Some (fst st) /\
        Genv.init_mem prog = Some (snd st).

    Definition final_state (st:state) (i:int) : Prop :=
      safely_halted Sem (Genv.globalenv prog) (fst st) (snd st) = Some (Vint i).

    Definition behaves : program_behavior -> Prop :=
      program_behaves step initial_state final_state (Genv.globalenv prog).

    Definition safe_state w ge st := 
      forall t w' st',
        star step ge st t st' ->
        possible_trace w t w' ->
          (exists i, final_state st' i) \/
          (exists t', exists st'', exists w'',
            step ge st' t' st'' /\
            possible_trace w' t' w'').

    Definition safe_prog w ge := forall st, initial_state st -> safe_state w ge st.

  End EXtSem_to_trace.

  Axiom forward_simulation_trace_forward : forall
      (F1 C1 V1 F2 C2 V2 :Type)
      (Sem1 : CompcertCoreSem F1 C1 V1 external_function)
      (Sem2 : CompcertCoreSem F2 C2 V2 external_function)

      (prog1 : program (fundef F1) V1)
      (prog2 : program (fundef F2) V2)

      (entry_points : list (ident * signature))

      (match_fun : fundef F1 -> fundef F2 -> Prop)
      (match_varinfo : V1 -> V2 -> Prop)

      (main_entry_point : In (prog_main prog1, main_sig) entry_points)
      (match_prog : match_program match_fun match_varinfo prog1 prog2)

      (fsim : ForwardSimulation Sem1 Sem2 
               (Genv.globalenv prog1) (Genv.globalenv prog2) entry_points (fun _ => eq)),

      forall beh,
        not_wrong beh ->
        behaves _ _ _ Sem1 prog1 beh ->
        behaves _ _ _ Sem2 prog2 beh.

  Axiom forward_simulation_trace_backward : forall
      (F1 C1 V1 F2 C2 V2 :Type)
      (Sem1 : CompcertCoreSem F1 C1 V1 external_function)
      (Sem2 : CompcertCoreSem F2 C2 V2 external_function)

      (prog1 : program (fundef F1) V1)
      (prog2 : program (fundef F2) V2)

      (entry_points : list (ident * signature))

      (match_fun : fundef F1 -> fundef F2 -> Prop)
      (match_varinfo : V1 -> V2 -> Prop)

      (main_entry_point : In (prog_main prog1, main_sig) entry_points)
      (match_prog : match_program match_fun match_varinfo prog1 prog2)

      (fsim : ForwardSimulation Sem1 Sem2 
               (Genv.globalenv prog1) (Genv.globalenv prog2) entry_points (fun _ => eq)),

      forall w beh,
        safe_prog _ _ _ Sem1 prog1 w (Genv.globalenv prog1) ->
        possible_behavior w beh ->
        behaves _ _ _ Sem2 prog2 beh ->
        behaves _ _ _ Sem1 prog1 beh.

  Axiom forward_simulation_trace_correct : forall
      (F1 C1 V1 F2 C2 V2 :Type)
      (Sem1 : CompcertCoreSem F1 C1 V1 external_function)
      (Sem2 : CompcertCoreSem F2 C2 V2 external_function)

      (prog1 : program (fundef F1) V1)
      (prog2 : program (fundef F2) V2)

      (entry_points : list (ident * signature))

      (match_fun : fundef F1 -> fundef F2 -> Prop)
      (match_varinfo : V1 -> V2 -> Prop)

      (main_entry_point : In (prog_main prog1, main_sig) entry_points)
      (match_prog : match_program match_fun match_varinfo prog1 prog2)

      (fsim : ForwardSimulation Sem1 Sem2 
               (Genv.globalenv prog1) (Genv.globalenv prog2) entry_points (fun _ => eq)),

      (forall w, safe_prog _ _ _ Sem1 prog1 w (Genv.globalenv prog1)) ->
      forall beh,
        (behaves _ _ _ Sem1 prog1 beh <-> behaves _ _ _ Sem2 prog2 beh).

End TRACE_CORRECTNESS.

*)
