(** *Semax Imports*)
Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.semax_ext_oracle.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.

Require Import concurrency.semax_to_juicy_machine.

(** *Erasure Imports*)
Require Import concurrency.erasure_signature.
Require Import concurrency.erasure_proof.
Require Import concurrency.erasure_safety.

(** **)

Module MainSafety .

  Module ErasureProof := erasure_proof.Parching.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  Module ErasureSafety := ErasureSafety.
  Import ErasureSafety.

  Parameters initU: DryMachine.Sch.
  Parameter init_rmap : JuicyMachine.SIG.ThreadPool.RES.res.
  Parameter init_pmap : DSEM.perm_map.
  Parameter init_rmap_perm:  match_rmap_perm init_rmap init_pmap.

  (*Definition local_erasure:= erasure initU init_rmap init_pmap init_rmap_perm*)
  Definition step_diagram:= ErasureProof.core_diagram.


  Section Initil.
   (* Import  *)
    Variables
      (CS : compspecs)
      (V : varspecs)
      (G : funspecs)
      (ext_link : string -> ident)
      (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
      (prog : program)
      (all_safe : semax_prog.semax_prog (Concurrent_Oracular_Espec CS ext_link) prog V G)
      (init_mem_not_none : Genv.init_mem prog <> None)
      (x: block)
      (block: (Genv.find_symbol (globalenv prog) (prog_main prog) = Some x)).

    
    Definition js_initial n := initial_machine_state CS V G ext_link prog all_safe
                                                     init_mem_not_none n.
    Definition dry_initial_perm :=
      getCurPerm( proj1_sig (init_m prog init_mem_not_none)).
    
    Definition dry_initial_core:=
      initial_core (juicy_core_sem cl_core_sem) 
                   (globalenv prog) (Vptr x Int.zero) nil.
    Definition ds_initial c := DSEM.initial_machine
                               dry_initial_perm
                               c.                   
    Lemma erasure_match: forall n,
        exists c, dry_initial_core = Some c /\ 
             ErasureProof.match_st (js_initial n) (ds_initial c).
    Proof. intros.
           destruct (dry_initial_core) eqn: AA.
           exists c; split; auto.
           constructor.
           - intro i.
             unfold js_initial, initial_machine_state, ErasureProof.JTP.containsThread; simpl;
             unfold ds_initial ,DSEM.initial_machine, ErasureProof.DTP.containsThread; simpl; auto.
           - intro i.
             unfold js_initial, initial_machine_state, ErasureProof.JTP.containsThread; simpl;
             unfold ds_initial ,DSEM.initial_machine, ErasureProof.DTP.containsThread; simpl; auto.
           - unfold ErasureProof.JTP.getThreadC, ErasureProof.DTP.getThreadC; simpl.
             intros. 
             transitivity (Krun c). f_equal.
             unfold initial_corestate.
             destruct (spr CS V G ext_link prog all_safe init_mem_not_none); simpl.
             destruct s;  simpl.
             unfold dry_initial_core in AA.
             destruct p.
             destruct p. congruence.
             admit.
           - intros.
             unfold ErasureProof.JTP.getThreadR;
               unfold ErasureProof.DTP.getThreadR; simpl.
             unfold dry_initial_perm. unfold initial_jm; simpl.
             destruct (spr CS V G ext_link prog all_safe init_mem_not_none) eqn:NN.
             simpl.
             unfold init_m.
             
             admit. (*Should follow from mem_compatible? *)
           - intros.
             unfold ErasureProof.JSEM.ThreadPool.lockRes;
               unfold ErasureProof.DSEM.ThreadPool.lockRes.
             auto.
           - unfold ErasureProof.DSEM.ThreadPool.lockRes.
             simpl. intros.  rewrite threadPool.find_empty in H0; inversion H0.
           - unfold ErasureProof.DSEM.ThreadPool.lockRes.
             simpl. intros.  rewrite threadPool.find_empty in H0; inversion H0.
    Admitted.
             
             
  
(*From semax_to_juicy_machine*)
(*Lemma juicy_safety: forall U rmap0 genv main vals js,
  semantics.initial_core (JMachineSem U (Some rmap0)) genv
         main vals = Some (U, nil, js) -> False.
*)

(*Theorem safety_initial_state (sch : schedule) (n : nat) :
  JuicyMachine.csafe (globalenv prog) (sch, nil, initial_machine_state n) (proj1_sig init_mem) n.
Proof.
  apply jmsafe_csafe, jmsafe_initial_state.
Qed.
*)
End Initil.
End MainSafety.
