Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.base.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compspecs.
Require Import VST.veric.semax_prog.
Require Import VST.veric.SequentialClight2.

Definition juicyspec : external_specification juicy_mem external_function unit
  := Build_external_specification juicy_mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False)
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => True).

Definition Espec : OracleKind.
 refine (Build_OracleKind unit (Build_juicy_ext_spec _ juicyspec _ _ _ _ _ _)).
Proof.
simpl; intros; contradiction.
simpl; intros; contradiction.
simpl; intros; intros ? ? ? ?; contradiction.
simpl; intros; contradiction.
repeat intro; auto.
repeat intro; auto.  
Defined.

Definition dryspec := juicy_dry_ext_spec_make _ juicyspec.

Lemma NullExtension_whole_program_sequential_safety:
   forall {CS: compspecs}
     (Jsub: forall ef se lv m t v m' (EFI : ef_inline ef = true) m1
       (EFC : Events.external_call ef se lv m t v m'), mem_sub m m1 ->
       exists m1' (EFC1 : Events.external_call ef se lv m1 t v m1'),
         mem_sub m' m1' /\ proj1_sig (Clight_core.inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC1) =
         proj1_sig (Clight_core.inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC))
     (prog: Clight.program) V G m,
     @semax_prog Espec CS prog tt V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core  (Clight_core.cl_core_sem (Clight.globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ unit (semax.genv_symb_injective)
          (Clight_core.cl_core_sem (Clight.globalenv prog)) dryspec
           (Clight.genv_genv 
            (Clight.Build_genv (Genv.globalenv prog) (Ctypes.prog_comp_env prog)) )
             n tt q m'.
Proof.
intros.
assert (dessicate : forall ef : external_function,
                   juicy_mem ->
                   @ext_spec_type juicy_mem external_function
                     (@OK_ty NullExtension.Espec) (@OK_spec NullExtension.Espec) ef ->
                   @ext_spec_type mem external_function 
                     (@OK_ty NullExtension.Espec) dryspec ef). {
  intros. assumption.
}
apply (@whole_program_sequential_safety CS NullExtension.Espec
 tt dryspec dessicate) with (V:=V) (G:=G); auto.
-
intros ??; contradiction.
-
split; intros; try assumption; try contradiction.
split; intros; try assumption.
split; repeat intro; auto.
split; repeat intro; auto.
-
hnf; intros; contradiction.
-
repeat intro; auto.
hnf. auto.
- intros ????????; auto.
Qed.

Lemma module_sequential_safety : (*TODO*)
   forall {CS: compspecs} (prog: Clight.program) (V: mpred.varspecs) 
      (G: mpred.funspecs) ora m f f_id f_b f_body args,
     let ge := Genv.globalenv prog in
     let ext_link := SeparationLogic.ext_link_prog prog in
     let spec := SeparationLogic.add_funspecs NullExtension.Espec ext_link G in
     let tys := sig_args (ef_sig f) in
     let rty := sig_res (ef_sig f) in
     let sem := juicy_core_sem (Clight_core.cl_core_sem (Clight.Build_genv ge (prog_comp_env prog))) in
     @semax_prog spec CS prog ora V G ->
     fun_id ext_link f = Some f_id ->
     Genv.find_symbol ge f_id = Some f_b ->
     Genv.find_funct  ge (Vptr f_b Ptrofs.zero) = Some f_body ->
     forall x : ext_spec_type (@OK_spec spec) f,
     ext_spec_pre (@OK_spec spec) f x (semax.genv_symb_injective ge) tys args ora m ->
     exists q,
       semantics.initial_core sem 
         0 (*additional temporary argument - TODO (Santiago): FIXME*)
             m q m
              (Vptr f_b Ptrofs.zero) args /\
       forall n, safeN_(genv_symb := @semax.genv_symb_injective _ _)(Hrel := fun _ => juicy_extspec.Hrel)
            sem  (upd_exit (@OK_spec spec) x (semax.genv_symb_injective ge)) 
           ge n ora q m.
Abort.