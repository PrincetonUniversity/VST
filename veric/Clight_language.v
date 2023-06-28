From iris.program_logic Require Import language.
From compcert.common Require Import AST Globalenvs Values.
From compcert.cfrontend Require Import Clight.
From VST.sepcomp Require Import extspec.
From VST.veric Require Import Clight_core.

Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree Values.block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.

Section language.

Context {Z} (Hspec : ext_spec Z).
Context (ge : genv).

Inductive gen_step c : (Memory.mem * Z) -> list unit -> CC_core -> (Memory.mem * Z) -> list CC_core -> Prop :=
| gen_step_core m z c' m' (Hcorestep : cl_step ge c m c' m') : gen_step c (m, z) [] c' (m', z) []
| gen_step_ext m z e args x ret m' z' c' (Hat_ext : cl_at_external c = Some (e, args)) (Hpre : ext_spec_pre Hspec e x (genv_symb_injective ge) (sig_args (ef_sig e)) args z m)
    (Hty : Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e)))
    (Hpost : ext_spec_post Hspec e x (genv_symb_injective ge) (sig_res (ef_sig e)) ret z' m')
    (Hafter_ext : cl_after_external ret c = Some c') :
    gen_step c (m, z) [] c' (m', z') [].

Definition Clight_language_mixin : LanguageMixin (λ v, Returnstate v Kstop) cl_halted gen_step.
Proof.
  split; try done.
  - destruct e; try done.
    destruct c; inversion 1; done.
  - inversion 1; subst.
    + apply cl_corestep_not_halted in Hcorestep; last apply Integers.Int.zero.
      destruct (cl_halted e); auto.
      by contradiction Hcorestep.
    + destruct e; done.
Qed.

Canonical Structure Clight_language := Language Clight_language_mixin.

End language.
