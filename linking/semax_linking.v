Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import JMeq.

Require Import msl.Coqlib2.

Require Import Integers.

Require Import juicy_mem.
Require Import juicy_extspec.
Require Import juicy_safety.
Require Import SequentialClight.
Require Export Ctypes.
Require Export Clight.
Require Import Clight_new.

Require Import pos.
Require Import val_casted.
Require Import linking. 
Require Import safety.

(** !!! Warnining: Currently depends on Axiom SequentialClight.module_sequential_safety !!! *)

Lemma semax_linking_preserves_safety :
  forall
  (N : pos) (plt : ident -> option 'I_N) 
  (modules : forall idx : 'I_N, program Clight.fundef type)
  (ora : Type) (ge : ge_ty) (main_id : ident) V G,

  let: spec := SeparationLogic.add_funspecs NullExtension.Espec G in
  let: sems := [fun idx : 'I_N => 
         mk_modsem (juicy_core_sem cl_core_sem) (Genv.globalenv (modules idx))] in 

  (** This particular assumption is stupid; 
    derives from the fact that [ef] maintains a function signature, 
    independent from [sig]. We must assume the two sigs. are equal. *)
  (forall (idx : 'I_N) (c : Modsem.C (sems idx))
          (ef : external_function) (sig : signature) 
          (args : list val),
     at_external (Modsem.sem (sems idx)) c = Some (ef, sig, args) ->
     sig = ef_sig ef) ->

  (** Postconditions imply return values are well-typed. *)
  (forall (ef : external_function) (x : ext_spec_type (@OK_spec spec) ef)
          (ge0 : Maps.PTree.t block) (rv : val) (z : @OK_ty spec) 
          (m : juicy_mem),
     ext_spec_post (@OK_spec spec) ef x ge0 (sig_res (ef_sig ef)) (Some rv) z m ->
     val_has_type_func rv (proj_sig_res (ef_sig ef))) ->

  (** The [plt] is well-formed wrt. the per-module global environments. *)
  (forall (fid : ident) (idx : 'I_N),
     plt fid = Some idx ->
     exists bf : block,
        Genv.find_symbol (Modsem.ge (sems idx)) fid = Some bf
     /\ exists f_body, 
          Genv.find_funct (Modsem.ge (sems idx)) (Vptr bf Int.zero) = Some f_body) ->
  
  (** Across modules, the symbol sets are *equal*. A weakening of this 
    assumption is possible if we assume that specs. are monotonic in some way 
    wrt. global symbols. *)
  (forall idx : 'I_N,
     Genv.genv_symb ge = Genv.genv_symb (Modsem.ge (sems idx))) ->

  (** We've proved soundness of each module in the Verifiable C logic. *)
  (forall idx : 'I_N, 
     @SeparationLogicSoundness.SoundSeparationLogic.CSL.semax_prog spec (modules idx) V G) ->

  (** We get that the linked program is safe in any memory state satisfying 
    the precondition for [main]. *)
  forall (x : ext_spec_type (@OK_spec spec) (main_ef main_id)) 
         (z : @OK_ty spec) 
         (m : juicy_mem) 
         (main_idx : 'I_N) 
         (main_b : block) 
         (args : list val),
    ext_spec_type (@OK_spec spec) (main_ef main_id) = unit ->
    fun_id (main_ef main_id) = Some main_id ->
    plt main_id = Some main_idx ->
    Genv.find_symbol (Modsem.ge (sems main_idx)) main_id = Some main_b ->
    ext_spec_pre (@OK_spec spec) (main_ef main_id) x (Genv.genv_symb ge)
                 (sig_args (ef_sig (main_ef main_id))) args z m ->
    exists l : linker N sems,
      initial_core (LinkerSem.coresem juicy_mem_ageable N sems plt) ge
                   (Vptr main_b Int.zero) args = Some l /\
      safeN (LinkerSem.coresem juicy_mem_ageable N sems plt)
            (upd_exit (ef:=main_ef main_id) (@OK_spec spec) x (Genv.genv_symb ge))
            ge (ageable.level m) z l m.
Proof.
move=> N plt modules ora ge main_id V G H H0 H1 H2 Hsemax. 
move=> x z m idx b args Hx Hy Hz Ha Hb.
apply: linker_preserves_safety=> //.
{ move=> fid idx0 Hplt; case: (H1 fid idx0 Hplt)=> bf0 []Hfind []f_body Hbody.
  by exists bf0. }
move=> ef fid idx0 bf args0 z0 m0 Hq Hr Hs x0 Ht.
case: (H1 fid idx0 Hr)=> bf0 []Hfind []f_body Hfunct.
move: (module_sequential_safety (modules idx0) V G z0 m0 ef fid bf0 f_body args0).
case/(_ (Hsemax idx0) Hq Hfind Hfunct x0 Ht)=> q0 []Hinit Hsafe; exists q0; split=> //.
by rewrite Hfind in Hs; case: Hs=> <-.
Qed.

