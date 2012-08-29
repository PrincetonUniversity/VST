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

Section MEMINSTR.
Definition value:= compcert.Values.val.

Definition block := compcert.Values.block. 

Inductive val :=
| Ptr : block -> Z -> val
| Val : value -> val.

Definition var := nat.
(*
Definition env := (var -> option (block * Z)%type). (*also finite*)
Axioms env_finite: forall E:env, exists n, forall m x, E m = Some x -> le m n.
*)

Parameter reverse_lookup : block * Z -> env -> env * var.
(*updates env when necessary*)

Record env : Type := mkEnv
  { domain: list var;
    env_proj :> var -> option (block * Z);
    dom_ax: forall n, ~ In n domain -> env_proj n = None}.

Definition env_ok (E:env) (j: meminj) : Prop :=
  forall n b off, E n = Some (b,off) -> exists p, j b = Some p.

(*Parameter env_inject : env -> meminj -> option env.*)

(*should be ok when applied to e, j s.t. env_ok_for e j*)
Definition env_inject (E:env) (j: meminj) (E':env):Prop :=
  forall n b' o', E' n = Some (b',o') <->
                  (exists b, exists o, exists oo, 
                     E n = Some(b,o) /\ j b = Some(b',oo) /\ o' = o+oo).

Lemma env_ok_inject: forall E j, env_ok E j -> exists E', env_inject E j E'.
  Proof. intros.
admit. (*held for previous representation
  exists (fun n => match E n with 
            None => None
          | Some (b,off) => match j b with 
                               None => None
                             | Some (b1,off1) => Some (b1, off+off1) end end).
  intros n b off.
  remember (E n) as z.
  destruct z; apply eq_sym in Heqz.
    destruct p as [b1 off1].
    specialize (H _ _ _ Heqz). destruct H as [[b2 off2] Hp].
    rewrite Hp.
    split; intros.
      inv H. exists b1. exists off1. exists off2; auto.
    destruct H as [b3 [off3 [off4 [X [Y Q]]]]]. subst.
      inv X. rewrite Y in Hp. inv Hp. trivial.
  split; intros. inv H0. 
    destruct H0 as [b3 [off3 [off4 [X [Y Q]]]]]. inv X.*)
Qed. 

Lemma env_inject_determ: forall E j E1 E2, env_inject E j E1 -> env_inject E j E2 -> env_proj E1 = env_proj E2.
  Proof. intros.
    extensionality n. remember (E1 n) as z.
    destruct z; apply eq_sym in Heqz.
                destruct p as [b o]. 
                destruct (H n b o) as [HE1 _].
                destruct (HE1 Heqz) as [b1 [off1 [off [HEn [J X]]]]]; subst. clear HE1 Heqz.
                destruct (H0 n b (off1 + off)) as [_ HE2].
                apply eq_sym. apply HE2.
                exists b1. exists off1. exists off. auto.
    remember (E2 n) as y.
    destruct y; apply eq_sym in Heqy; trivial.
                destruct p as [b o]. 
                destruct (H0 n b o) as [HE2 _].
                destruct (HE2 Heqy) as [b1 [off1 [off [HEn [J X]]]]]; subst. clear HE2 Heqy.
                destruct (H n b (off1 + off)) as [_ HE1].
                rewrite Heqz in HE1.
                apply HE1. clear HE1.
                exists b1. exists off1. exists off. auto.
  Qed.
Lemma meminj_compose_split: forall j1 j2 b b2 off,
      Mem.meminj_compose j1 j2 b = Some (b2, off) ->
      exists b1, exists off1, j1 b = Some (b1,off1) /\
                 exists off2, j2 b1 = Some (b2,off2) /\ off =off1 + off2.
  Proof.
    intros.
    unfold Mem.meminj_compose in H.
    remember (j1 b) as z.
    destruct z. destruct p as [b1 off1].
      exists b1. exists off1. split; trivial. 
      remember (j2 b1) as y.
      destruct y. destruct p as [b3 off2]. inv H.
        exists off2. split; trivial.
      inv H.
    inv H.
  Qed. 
Lemma Env_inject_compose: forall E j1 E1 j2 E2, 
      env_inject E j1 E1 ->
      env_inject E1 j2 E2 ->
      env_inject E (Mem.meminj_compose j1 j2) E2.
  Proof.
    intros. intros n; intros.
    split; intros.
      apply H0 in H1. clear H0.
      destruct H1 as [b1 [off1 [off2 [E1n [J2b1 X]]]]]. subst.
      apply H in E1n.
      destruct E1n as [b2 [off3 [off4 [E2n [Y X]]]]]. subst.
      exists b2. exists off3. exists (off4 + off2). split; trivial.
      split. unfold Mem.meminj_compose. rewrite Y. rewrite J2b1. trivial.
      rewrite <- Zplus_assoc. trivial.
    destruct H1 as [b1 [off1 [off2 [En [J X]]]]]. subst.
      apply meminj_compose_split in J. destruct J as [b2 [off3 [J1 [off4 [J2 X]]]]]. subst.
      assert ( E1 n = Some (b2, off1 + off3)).
         apply H. rewrite En. exists b1. exists off1. exists off3. auto.
      apply H0. rewrite H1. exists b2. exists (off1 + off3). exists off4. rewrite <- Zplus_assoc. auto.
  Qed.    

Lemma Env_ok1: forall j1 j2 E,
  env_ok E (Mem.meminj_compose  j1 j2) -> env_ok E j1.
  Proof.
    intros.
    intros n; intros.
    specialize (H _ _ _ H0). 
    destruct H as [[b1 off1] X].
    remember (j1 b) as z.
    destruct z. exists p; trivial.
    apply eq_sym in Heqz.
    unfold Mem.meminj_compose in X.
    rewrite Heqz in X. inv X. 
  Qed. 

Lemma Env_ok2: forall E j1 j2 E1,
  env_ok E (Mem.meminj_compose  j1 j2) ->
  env_inject E j1 E1 ->
  env_ok E1 j2.
  Proof.
    intros.
    intros n; intros.
    apply H0 in H1. destruct H1 as [b1 [off1 [off2 [En [J1 X]]]]]. subst.
    specialize (H _ _ _ En). destruct H as [[b2 off3] X].
    unfold Mem.meminj_compose in X.
    rewrite J1 in X.
    remember (j2 b) as J2.
    destruct J2. exists p; trivial. inv X.
  Qed. 
Lemma Env_ok3: forall E j1 j2 E1 E2,
  env_ok E (Mem.meminj_compose  j1 j2) ->
  env_inject E (Mem.meminj_compose j1 j2) E2 -> 
  env_inject E j1 E1 ->
  env_inject E1 j2 E2.
  Proof.
    intros.
    assert (OK1 := Env_ok1 _ _ _ H).
    assert (OK2:= Env_ok2 _ _ _ _ H H1).
    apply env_ok_inject in OK2. destruct OK2 as [E'' X].
    assert (Z:= Env_inject_compose _ _ _ _ _ H1 X).
    apply (env_inject_determ _ _ _ _ H0) in Z. hnf. intros.  rewrite Z. apply X.
  Qed.
  
(*Lemma env_inject_implies_env_ok: forall E j E',
  env_inject E j E' -> env_ok E j.
(*  Does not hold*)
  Proof.
    unfold env_inject  , env_ok; intros.
*)

Record Typ : Type := mkTyp {
  typA :> Type;
  typR: meminj -> typA -> typA -> Prop;
  typR_extend: typA -> typA -> Prop
}.

(*
Parameter inject_incr : meminj -> meminj -> Prop.

Parameter mem_inject : meminj -> mem -> mem -> Prop.

Notation "Mem.inject" := mem_inject.
*)

Record MemProg (A: Typ) := mkMemProg {
  mem_prog : env * mem -> option (A * env * mem);
  memprog_axiom_inject : 
    forall j m1 m2 e1 e1' a1 e2 m1', 
      Mem.inject j m1 m2 -> 
      env_inject e1 j e2 -> 
      mem_prog (e1, m1) = Some (a1, e1', m1') -> 
    exists a2, exists m2', exists e2',
      mem_prog (e2, m2) = Some (a2, e2', m2') /\ 
    exists! j', (*hope: j' is uniquely determined by the memprog, e1, m1, e2, m2 and j*)
        env_inject e1' j' e2' /\ inject_incr j j' /\
        typR A j' a1 a2 /\ Mem.inject j' m1' m2';
  memprog_axiom_extend : 
    forall m1 m2 e1 e1' a1 m1', 
      Mem.extends m1 m2 -> 
      mem_prog (e1, m1) = Some (a1, e1', m1') -> 
    exists a2, exists m2', 
      mem_prog (e1, m2) = Some (a2, e1', m2') /\
        typR_extend A a1 a2 /\ Mem.extends m1' m2'
}.
      
Definition ValTyp : Typ := mkTyp Values.val (val_inject) Val.lessdef.

Module MemInstrModule.
(* An axiom for passes that use memory injections. *)
Section MemInstr_simulation_inject. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record MemInstr_simulation_inject := {
    core_data : Type;

    match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop;

    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    (* later: add core_diagram, core_initial and core_halted, and maybe macth_siinj*)

    core_at_external : 
      forall cd js st1 m1 st2 m2 e vals1,
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists ms, check_injectlist js m1 ms m2 /\
          exists vals2, Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);


End MemInstrModule.

Definition siminj (j: meminj) (m1 m2 : mem) :=
  (forall b, ~(Mem.valid_block m1 b) -> j b = None) /\
  (forall b b' delta, j b = Some(b', delta) -> Mem.valid_block m2 b').

Fixpoint injlist_compose (j : list meminj) : meminj :=
  match j with 
     nil => fun b => Some (b,0)
  | cons h t => Mem.meminj_compose h (injlist_compose t)
  end.

Module Sim_inj.
(* An axiom for passes that use memory injections. *)
Section Forward_simulation_inject. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

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

  Record Forward_simulation_inject := {
    core_data : Type;
    num_passes : nat; (*gives length of js ms,...*)

    match_state : core_data -> list meminj -> C1 -> mem -> C2 -> mem -> Prop;
   
    match_state_num_passes: forall cd js st1 m1 st2 m2,
        match_state cd js st1 m1 st2 m2 -> length js = num_passes;

    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

(*Maybe we need an axiom like this?
    thread_axiom: forall cd j m1 c1 m2 c2, match_state cd j c1 m1 c2 m2 ->
             (*we want maybe same sequence of memops to be applied in both forward_modifications*)
               allowed_forward_modifications m1 m1' ->
               allowed_forward_modifications m2 m2' ->
           exists j', incject_incr j j' /\ inject_separated j j' m1 m2
               match_state cd j' c1 m1' c2 m2';
*)

    match_state_siminj :
      forall cd j st1 m1 st2 m2,
        match_state cd j st1 m1 st2 m2 -> siminj (injlist_compose j) m1 m2;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          Forall2 inject_incr j j' /\
          inject_separated (injlist_compose j) (injlist_compose j') m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord cd' cd);


    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals1 c1 m1,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          initial_mem Sem1 ge1 m1 ->
          let js := mkInjections m1 num_passes in
           (*was: let js  map (fun m => Mem.flat_inj (Mem.nextblock m1)) ms in*)
(*          let m2 := last ms m1 in
          let vals2 := last valss vals1 in*)
           (*Lenb: the following two conditions appear to be needed for composition inj_inj*)
           (*Mem.inject (Mem.flat_inj (Mem.nextblock m2)) m2 m2 ->
           F orall2 (val_inject (Mem.flat_inj (Mem.nextblock m2))) vals' vals' ->*)

          (*check_valslist js vals1 valss ->
          Forall2 (Val.has_type) vals2 (sig_args sig) ->*)
          (*check_injectlist js m1 ms ->*)
(*          Forall2 (Val.has_type) vals1 (sig_args sig) ->*)
          exists cd, exists c2, exists vals2, exists m2, 
            make_initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            initial_mem Sem2 ge2 m2 /\
            match_state cd js c1 m1 c2 m2;


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
    core_halted : forall cd js c1 m1 c2 m2 (v1:int),
      match_state cd js c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         exists ms, check_injectlist js m1 ms m2);
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
      forall cd js st1 m1 st2 m2 e vals1,
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists ms, check_injectlist js m1 ms m2 /\
          exists vals2, Forall2 (val_inject (injlist_compose js)) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);
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
      forall cd js js' st1 st2 m1 ms e vals1 (*vals2*) ret1 rets m1' ms' m2 m2' ret2,
        check_injectlist js m1 ms m2->
        match_state cd js st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
(*        Mem.inject j m1 m2 ->
        at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->*)
      
        Forall2 inject_incr js js' ->
        inject_separated (injlist_compose js) (injlist_compose js') m1 m2 ->
        check_injectlist js' m1' ms' m2' ->
        check_returns js' ret1 rets ret2 ->

        mem_square js m1 ms m1' ms' ->

        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' js' st1' m1' st2' m2'

    }.

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
