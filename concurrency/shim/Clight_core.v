Require Import VST.sepcomp.semantics.
Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relations.


Require Import compcert.exportclight.Clightdefs.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memdata.
Require Import compcert.common.Memtype.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.


Require Import EqNat.  (* do we need this? *)
Require Import VST.msl.Coqlib2.
Require compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.cfrontend.Clight.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.common.core_semantics.


Inductive CC_core : Type :=
    CC_core_State : function ->
            statement -> cont -> env -> temp_env -> CC_core
  | CC_core_Callstate : fundef -> list val -> cont -> CC_core
  | CC_core_Returnstate : val -> cont -> CC_core.

Definition CC_core_to_CC_state (c:CC_core) (m:mem) : state :=
  match c with
     CC_core_State f st k e te => State f st k e te m
  |  CC_core_Callstate fd args k => Callstate fd args k m
  | CC_core_Returnstate v k => Returnstate v k m
 end.
Definition CC_state_to_CC_core (c:state): CC_core * mem :=
  match c with
     State f st k e te m => (CC_core_State f st k e te, m)
  |  Callstate fd args k m => (CC_core_Callstate fd args k, m)
  | Returnstate v k m => (CC_core_Returnstate v k, m)
 end.

Lemma  CC_core_CC_state_1: forall c m,
   CC_state_to_CC_core  (CC_core_to_CC_state c m) = (c,m).
  Proof. intros. destruct c; auto. Qed.

Lemma  CC_core_CC_state_2: forall s c m,
   CC_state_to_CC_core  s = (c,m) -> s= CC_core_to_CC_state c m.
  Proof. intros. destruct s; simpl in *.
      destruct c; simpl in *; inv H; trivial.
      destruct c; simpl in *; inv H; trivial.
      destruct c; simpl in *; inv H; trivial.
  Qed.

Lemma  CC_core_CC_state_3: forall s c m,
   s= CC_core_to_CC_state c m -> CC_state_to_CC_core  s = (c,m).
  Proof. intros. subst. apply CC_core_CC_state_1. Qed.

Lemma  CC_core_CC_state_4: forall s, exists c, exists m, s =  CC_core_to_CC_state c m.
  Proof. intros. destruct s.
             exists (CC_core_State f s k e le). exists m; reflexivity.
             exists (CC_core_Callstate fd args k). exists m; reflexivity.
             exists (CC_core_Returnstate res k). exists m; reflexivity.
  Qed.

Lemma CC_core_to_CC_state_inj: forall c m c' m',
     CC_core_to_CC_state c m = CC_core_to_CC_state c' m' -> (c',m')=(c,m).
  Proof. intros.
       apply  CC_core_CC_state_3 in H. rewrite  CC_core_CC_state_1 in H.  inv H. trivial.
  Qed.

Lemma cl_corestep_not_halted : forall ge m q m' q' i,
  step2corestep (part_semantics2 ge) q m q' m' -> ~final_state q i.
Proof.
  repeat intro.
  inv H0.
  inv H.
  inv H0.
Qed.

Definition cl_core_sem (ge : genv) := sem2coresem (part_semantics2 ge) (cl_corestep_not_halted ge).

Definition at_external := at_external.  (* Temporary definition for compatibility between CompCert 3.3 and new-compcert *)

