Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import onepile.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_onepile.

Instance OnePileCompSpecs : compspecs. make_compspecs prog. Defined.

Section Onepile_VSU.
Variable M: MallocFreeAPD.
Variable PILE: PileAPD. (*onepile is parametric in a pile predicate structure*)

Definition one_pile (sigma: option (list Z)) (gv: globals): mpred :=
 match sigma with
 | None => data_at_ Ews (tptr tpile) (gv _the_pile)
 | Some il => EX p:val, data_at Ews (tptr tpile) p (gv _the_pile) *
                        pilerep PILE il p * pile_freeable PILE p
 end.

Lemma make_onepile: forall gv,
  data_at_ Ews (tptr (Tstruct onepile._pile noattr)) (gv onepile._the_pile)
   |-- one_pile None gv.
Proof.
intros. cancel.
Qed.

Definition ONEPILE: OnePileAPD := Build_OnePileAPD one_pile.

  Definition Onepile_ASI: funspecs := OnepileASI M ONEPILE.

(*onepile's Imported specs.*)
  Definition onepile_imported_specs:funspecs := 
     [ Pile_new_spec M PILE; Pile_add_spec M PILE; Pile_count_spec PILE].
(*TODO: at present we're not permitted to overapproximate here: if we define
      onepile_imported_specs := PileASI PILE.  
  ie include the spec Pile_free_spec PILE, then the bodyproofs below won't fail, 
  but the first (usually automatically discharged) subgoal of tactic mkComponent 
  in the definition of OnepileComponent below will fail.*)

  Definition onepile_internal_specs: funspecs := (*surely_malloc_spec::*)Onepile_ASI.

  Definition OnepileVprog: varspecs. mk_varspecs prog. Defined.
  Definition OnepileGprog: funspecs := onepile_imported_specs ++ onepile_internal_specs.

Lemma body_Onepile_init: semax_body OnepileVprog OnepileGprog f_Onepile_init (Onepile_init_spec M ONEPILE).
Proof.
start_function.
forward_call gv.
Intros p.
simpl onepile. unfold one_pile.
forward.
simpl onepile. unfold one_pile.
Exists p.
entailer!.
Qed.

Lemma body_Onepile_add: semax_body OnepileVprog OnepileGprog f_Onepile_add (Onepile_add_spec M ONEPILE).
Proof.
start_function.
simpl onepile. unfold one_pile.
Intros p.
forward.
forward_call (p,n,sigma,gv).
forward.
simpl onepile. unfold one_pile.
Exists p.
entailer!.
Qed.

Lemma body_Onepile_count: semax_body OnepileVprog OnepileGprog f_Onepile_count (Onepile_count_spec ONEPILE).
Proof.
start_function.
simpl onepile. unfold one_pile.
Intros p.
forward.
forward_call (p,sigma).
forward.
Exists p.
entailer!.
Qed.

  Lemma onepile_Init_aux gv: headptr (gv _the_pile) ->
    globvar2pred gv (_the_pile, v_the_pile)
    |-- data_at_ Ews (tptr (Tstruct _pile noattr)) (gv _the_pile).
  Proof. intros.
    unfold globvar2pred. simpl.
         rewrite sepcon_emp.
    destruct H as [b Hb]; rewrite Hb in *.
    eapply derives_trans. 
    + apply mapsto_zeros_memory_block. apply writable_readable. apply writable_Ews.
    + rewrite <- memory_block_data_at_; simpl; trivial.
      apply headptr_field_compatible; trivial. exists b; trivial. cbv; trivial. simpl; rep_lia.
      econstructor. reflexivity. apply Z.divide_0_r.
  Qed.


  Lemma onepile_Init: VSU_initializer prog (one_pile None).
  Proof. InitGPred_tac. unfold one_pile. normalize. apply data_at_data_at_. Qed.

Definition OnepileVSU: @VSU NullExtension.Espec
      nil onepile_imported_specs ltac:(QPprog prog) Onepile_ASI (one_pile None).
Proof.
 mkVSU prog onepile_internal_specs.
    + solve_SF_internal body_Onepile_init.
    + solve_SF_internal body_Onepile_add.
    + solve_SF_internal body_Onepile_count.
    + apply onepile_Init.
  Qed.

End Onepile_VSU.
