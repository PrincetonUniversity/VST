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
(*
Definition one_pile' (sigma: option (list Z)) (gv: globals) : mpred :=
 match sigma with
 | None =>  data_at_ Ews (tptr tpile) (*memory_block Ews 4*) (gv _the_pile)
            (*data_at Ews (tptr tpile) nullval (gv _the_pile)*)
 | Some il => EX p:val, data_at Ews (tptr tpile) p (gv _the_pile) *
                        pilerep PILE il p * pile_freeable PILE p
 end.
Definition one_pile (sigma: option (list Z)) (gv: globals) : mpred := 
 !!(headptr (gv _the_pile)) && one_pile' sigma gv.
*)
Definition one_pile (sigma: option (list Z)) (gv: globals) : mpred := 
(* !!(headptr (gv _the_pile)) &&*)
match sigma with
 | None =>  data_at_ Ews (tptr tpile) (*memory_block Ews 4*) (gv _the_pile)
            (*data_at Ews (tptr tpile) nullval (gv _the_pile)*)
 | Some il => EX p:val, data_at Ews (tptr tpile) p (gv _the_pile) *
                        pilerep PILE il p * pile_freeable PILE p
 end.

Lemma make_onepile: forall gv, (*headptr (gv _the_pile) ->*)
  data_at_ Ews (tptr (Tstruct onepile._pile noattr)) (gv onepile._the_pile)
   |-- one_pile None gv.
Proof.
intros.
unfold onepile, one_pile. entailer!.
Qed.
(*
Lemma make_onepile: forall gv, headptr (gv _the_pile) ->
  data_at Ews (tptr (Tstruct onepile._pile noattr)) nullval (gv onepile._the_pile)
   = one_pile None gv.
Proof.
intros.
unfold one_pile. simpl. apply pred_ext.
+ entailer!.
+ entailer!.
Qed.*)
(*
  Lemma MyInitData gv (H: headptr (gv _the_pile)):
        initialize.gv_globvar2pred gv (_the_pile, v_the_pile) gv 
        = data_at Ews (tptr tpile) nullval (gv _the_pile).
  Proof. unfold initialize.gv_globvar2pred. simpl.
         unfold initialize.gv_lift2, initialize.gv_lift0; simpl.
         rewrite predicates_sl.sepcon_emp. forget (gv _the_pile) as p.
         erewrite <- (mapsto_data_at'' Ews (tptr tpile)); trivial. clear - H.
         unfold tpile, tptr. rewrite mapsto_size_t_tptr_nullval.
         reflexivity.
  Qed.
  Lemma onepile_Init gv: InitGPred (Vardefs prog) gv |-- one_pile None gv.
  Proof. unfold InitGPred, one_pile. simpl; Intros. rewrite sepcon_emp, MyInitData; trivial; entailer!. Qed.
*)
  Lemma onepile_Init_aux gv: headptr (gv _the_pile) ->
    initialize.gv_globvar2pred gv (_the_pile, v_the_pile) gv
    |-- data_at_ Ews (tptr (Tstruct _pile noattr)) (gv _the_pile).
  Proof. intros.
    unfold initialize.gv_globvar2pred, initialize.gv_globvar2pred. simpl.
         unfold initialize.gv_lift2, initialize.gv_lift0; simpl.
         rewrite predicates_sl.sepcon_emp.
    destruct H as [b Hb]; rewrite Hb in *.
    eapply derives_trans. 
    + apply mapsto_zeros_memory_block. apply writable_readable. apply writable_Ews.
    + rewrite <- memory_block_data_at_; simpl; trivial.
      apply headptr_field_compatible; trivial. exists b; trivial. cbv; trivial. simpl; rep_lia.
      econstructor. reflexivity. apply Z.divide_0_r.
  Qed.

  Lemma onepile_Init_aux2 gv: headptr (gv _the_pile) ->
    initialize.gv_globvar2pred gv (_the_pile, v_the_pile) gv
    |--  one_pile None gv.
  Proof. intros. sep_apply onepile_Init_aux. apply make_onepile; trivial. Qed.

  Lemma onepile_Init gv: InitGPred (Vardefs prog) gv |-- one_pile None gv.
  Proof. unfold InitGPred. simpl; Intros. sep_apply onepile_Init_aux2; trivial. simpl; trivial. Qed.

Definition ONEPILE: OnePileAPD := Build_OnePileAPD one_pile(* OnePileCompSpecs make_onepile*) (*_  onepile_Init*).

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
simpl onepile; unfold one_pile(*; simpl one_pile'*); Intros.
(*specialize (memory_block_data_at_ Ews (tptr tpile)); simpl; intros X.
rewrite X; clear X.
2:{ red; simpl. destruct HP_the_pile. rewrite H in *. repeat split; trivial.
    eapply align_compatible_rec_by_value. cbv; reflexivity. apply Z.divide_0_r. }*)
forward.
simpl onepile; unfold one_pile(*; simpl one_pile'*).
Exists p.
entailer!.
Qed.

Lemma body_Onepile_add: semax_body OnepileVprog OnepileGprog f_Onepile_add (Onepile_add_spec M ONEPILE).
Proof.
start_function.
simpl onepile; unfold one_pile(*; simpl one_pile'*); Intros.
Intros p.
forward.
forward_call (p,n,sigma,gv).
forward.
simpl onepile; unfold one_pile(*; simpl one_pile'*).
Exists p.
entailer!.
Qed.

Lemma body_Onepile_count: semax_body OnepileVprog OnepileGprog f_Onepile_count (Onepile_count_spec ONEPILE).
Proof.
start_function.
simpl onepile; unfold one_pile(*; simpl one_pile'*); Intros.
Intros p.
forward.
forward_call (p,sigma).
forward.
simpl onepile; unfold one_pile(*; simpl one_pile'*).
Exists p.
entailer!.
Qed.
(*hold but dead
Lemma GG: globvar2pred = initialize.globvar2pred. reflexivity. Qed.

  Lemma globEntailsInitPred g:
        globvar2pred (globals_of_env (Clight_seplog.mkEnv g [] [])) (onepile._the_pile, onepile.v_the_pile)
                    (Clight_seplog.mkEnv g [] [])
        |-- one_pile None (globals_of_env (Clight_seplog.mkEnv g [] [])).
  Proof. unfold one_pile, one_pile'. rewrite GG, initialize.globvar2pred_char_gv. simpl. unfold initialize.gv_globvar2pred. simpl.
         unfold initialize.gv_lift2, initialize.gv_lift0; simpl.
         rewrite predicates_sl.sepcon_emp. rewrite mapsto_isptr; Intros. apply global_is_headptr in H.
         erewrite <- (mapsto_data_at'' Ews (tptr tpile)); trivial. entailer!. clear - H.
         unfold tpile, tptr. rewrite mapsto_size_t_tptr_nullval. apply derives_refl.
  Qed.*)

  Definition OnepileComponent: @Component NullExtension.Espec OnepileVprog _ 
      nil onepile_imported_specs prog Onepile_ASI (one_pile None) onepile_internal_specs.
  Proof.
    mkComponent. 
    + solve_SF_internal body_Onepile_init.
    + solve_SF_internal body_Onepile_add.
    + solve_SF_internal body_Onepile_count.
    + intros. (* unfold InitGPred, one_pile; simpl. entailer!.
      rewrite MyInitData; trivial; cancel.*) 
      sep_apply (onepile_Init gv); simpl; cancel.
  Qed.

Definition OnepileVSU: @VSU NullExtension.Espec OnepileVprog _ 
      nil onepile_imported_specs prog Onepile_ASI (one_pile None).
  Proof. eexists; apply OnepileComponent. Qed.
End Onepile_VSU.
