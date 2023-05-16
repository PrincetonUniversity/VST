Require Import VST.veric.Clight_base.
Require Export compcert.lib.Axioms.
Require Import compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Floats.
Require Export compcert.common.AST.
Require Export compcert.common.Values.
Require Export compcert.cfrontend.Ctypes.
Require Export compcert.cfrontend.Clight.
Require Export VST.sepcomp.Address.
Require Export VST.msl.eq_dec.
Require Export VST.msl.shares.
Require Export VST.veric.tycontext.
Require Export VST.veric.change_compspecs.
Require Export VST.veric.mpred.
Require Export VST.veric.expr.
Require Export VST.veric.expr2.
Require Export VST.veric.expr_lemmas.
Require Export VST.veric.Clight_lemmas.
Require Export VST.veric.composite_compute.
Require Export VST.veric.align_mem.
Require Export VST.veric.shares.
Require Export VST.veric.seplog.
Require Export VST.veric.Clight_seplog.
Require Export VST.veric.Clight_assert_lemmas.
Require Export VST.veric.extend_tc.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.valid_pointer.
Require Export VST.veric.external_state.
Require Export VST.veric.Clight_initial_world.
Require Export VST.veric.initialize.
Require Export VST.veric.semax.
Require Export VST.veric.juicy_mem_lemmas.
Require Export VST.veric.semax_straight.
Require Export VST.veric.semax_call.
Require Export VST.veric.semax_prog.
Require Export VST.veric.semax_ext.
Import LiftNotation.
Import Ctypes Clight.
Export expr.

#[export] Existing Instance EqDec_ident.
#[export] Existing Instance EqDec_byte.
#[export] Existing Instance EqDec_memval.
#[export] Existing Instance EqDec_quantity.

Global Opaque mpred.

#[export] Hint Resolve any_environ : typeclass_instances.

Section mpred.

Context `{!heapGS Σ}.

(* Somehow, this fixes a universe collapse issue that will occur if fool is not defined.
Definition fool := @map _ Type (fun it : ident * type => mpred).*)

Fixpoint ext_link_prog' (dl: list (ident * globdef fundef type)) (s: String.string) : option ident :=
 match dl with
 | (id, Gfun (External EF_malloc _ _ _)) :: dl' =>
      if String.string_dec s "_malloc" then Some id else ext_link_prog' dl' s
 | (id, Gfun (External EF_free _ _ _)) :: dl' =>
      if String.string_dec s "_free" then Some id else ext_link_prog' dl' s
 | (id, Gfun (External (EF_external s' _) _ _ _)) :: dl' =>
      if String.string_dec s s' then Some id else ext_link_prog' dl' s
 | (id, Gfun (External (EF_builtin s' _) _ _ _)) :: dl' =>
      if String.string_dec s s' then Some id else ext_link_prog' dl' s
 | _ :: dl' =>
     ext_link_prog' dl' s
 | nil => None
 end.

Definition ext_link_prog (p: program) (s: String.string) : ident :=
  match ext_link_prog' (prog_defs p) s with Some id => id | None => 1%positive end.

Definition globals := ident -> val.


(*We're exporting the step-indexed version so that semax_fun_id doesn't syntactically change*)
Definition func_ptr ge E id (f: funspec) (v: val): mpred := seplog.func_ptr_si ge E id f v.

(*veric.seplog has a lemma that weakens the hypothesis here to funspec_sub_si*)
Lemma func_ptr_mono ge E id fs gs v (H:funspec_sub E fs gs): func_ptr ge E id fs v ⊢ func_ptr ge E id gs v.
Proof. apply funspec_sub_implies_func_prt_si_mono; done. Qed.

Lemma func_ptr_isptr: forall ge E id spec f, func_ptr ge E id spec f ⊢ ⌜isptr f⌝.
Proof. apply seplog.func_ptr_si_isptr. Qed.

Definition type_of_funsig (fsig: funsig) :=
   Tfunction (type_of_params (fst fsig)) (snd fsig) cc_default.

Definition with_ge (ge: genviron) (G: environ->mpred) : mpred :=
     G (mkEnviron ge (Map.empty _) (Map.empty _)).

Fixpoint arglist (n: positive) (tl: typelist) : list (ident*type) :=
 match tl with
  | Tnil => nil
  | Tcons t tl' => (n,t):: arglist (n+1)%positive tl'
 end.

Definition loop_nocontinue_ret_assert := @loop2_ret_assert Σ.

(* Misc lemmas *)
Lemma typecheck_lvalue_sound {CS: compspecs} :
  forall Delta rho e,
    typecheck_environ Delta rho ->
    tc_lvalue Delta e rho ⊢ ⌜is_pointer_or_null (eval_lvalue e rho)⌝.
Proof.
eapply expr_lemmas4.typecheck_lvalue_sound; eauto.
Qed.

Lemma typecheck_expr_sound {CS: compspecs} :
  forall Delta rho e,
    typecheck_environ Delta rho ->
    tc_expr Delta e rho ⊢ ⌜tc_val (typeof e) (eval_expr e rho)⌝.
Proof.
eapply expr_lemmas4.typecheck_expr_sound; eauto.
Qed.


(***************LENB: ADDED THESE LEMMAS IN INTERFACE************************************)

Lemma tc_expr_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  tc_expr(CS := CS) Delta e rho ⊢ tc_expr (CS := CS') Delta e rho.
Proof. intros. destruct CSUB as [CSUB _]. apply (extend_tc.tc_expr_cenv_sub CSUB e rho Delta). Qed.

Lemma tc_lvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  tc_lvalue (CS := CS) Delta e rho ⊢ tc_lvalue (CS := CS') Delta e rho.
Proof. intros; simpl. destruct CSUB as [CSUB _]. apply (extend_tc.tc_lvalue_cenv_sub CSUB e rho Delta). Qed.

Lemma tc_exprlist_cspecs_sub {CS CS'} (CSUB: cspecs_sub  CS CS') Delta rho: forall types e,
  tc_environ Delta rho ->
  tc_exprlist (CS := CS) Delta types e rho ⊢ tc_exprlist (CS := CS') Delta types e rho.
Proof. intros. destruct CSUB as [CSUB _]. apply (extend_tc.tc_exprlist_cenv_sub CSUB Delta rho). Qed.

Lemma eval_exprlist_cspecs_sub {CS CS'} (CSUB: cspecs_sub  CS CS') Delta rho (TCD: tc_environ Delta rho):
  forall types e,
  tc_exprlist (CS := CS) Delta types e rho ⊢ ⌜@eval_exprlist CS types e rho = @eval_exprlist CS' types e rho⌝.
Proof. intros. destruct CSUB as [CSUB _]. eapply (expr_lemmas.typecheck_exprlist_sound_cenv_sub CSUB); eassumption. Qed.

Lemma denote_tc_assert_tc_bool_cs_invariant {CS CS'} b E:
  denote_tc_assert (CS := CS) (tc_bool b E) = denote_tc_assert (CS := CS') (tc_bool b E).
Proof. unfold tc_bool. destruct b; reflexivity. Qed.

Lemma tc_temp_id_cspecs_sub {CS CS'} (CSUB: cspecs_sub  CS CS') Delta rho e i:
  tc_environ Delta rho -> tc_temp_id i (typeof e) (CS := CS) Delta e rho ⊢ tc_temp_id i (typeof e) (CS := CS') Delta e rho.
Proof.
  intros. unfold tc_temp_id, typecheck_temp_id; simpl.
  destruct ((temp_types Delta) !! i); last done.
  rewrite !denote_tc_assert_andp.
  iIntros "H"; iSplit.
  + iDestruct "H" as "[H _]"; rewrite (@denote_tc_assert_tc_bool_cs_invariant CS' CS) //.
  + rewrite tc_bool_e; iDestruct "H" as (?) "?".
    iApply expr2.neutral_isCastResultType.
Qed.

Lemma castexpropt_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  tc_expropt (CS := CS) Delta ret t rho ⊢ ⌜@cast_expropt CS ret t rho = @cast_expropt CS' ret t rho⌝.
Proof.
  destruct CSUB; apply RA_return_castexpropt_cenv_sub; done.
Qed.

Lemma RA_return_cast_expropt_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e t R rho,
  tc_environ Delta rho ->
  tc_expropt (CS := CS) Delta e t rho ∧ RA_return R (@cast_expropt CS e t rho) (id rho)
  ⊢ RA_return R (@cast_expropt CS' e t rho) (id rho).
Proof.
  intros. rewrite castexpropt_cenv_sub //.
  iIntros "(-> & $)".
Qed.

(********************************************* LENB: END OF ADDED LEMMAS********************)

(* End misc lemmas *)

Fixpoint unfold_Ssequence c :=
  match c with
  | Ssequence c1 c2 => unfold_Ssequence c1 ++ unfold_Ssequence c2
  | _ => c :: nil
  end.

Fixpoint nocontinue s :=
 match s with
 | Ssequence s1 s2 => if nocontinue s1 then nocontinue s2 else false
 | Sifthenelse _ s1 s2 => if nocontinue s1 then nocontinue s2 else false
 | Sswitch _ sl => nocontinue_ls sl
 | Sgoto _ => false
 | Scontinue => false
 | Slabel _ s => nocontinue s
 | _ => true
end
with nocontinue_ls sl :=
 match sl with LSnil => true | LScons _ s sl' => if nocontinue s then nocontinue_ls sl' else false
 end.

End mpred.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Parameter semax: forall {Σ : gFunctors} `{!heapGS Σ} {Espec : OracleKind}
  `{!externalGS (OK_ty(Σ := Σ)) Σ} {C : compspecs},
  coPset → tycontext → @assert Σ → statement → @ret_assert Σ → Prop.

Parameter semax_func: forall {Σ : gFunctors} `{!heapGS Σ} {Espec : OracleKind}
  `{!externalGS (OK_ty(Σ := Σ)) Σ} (V : varspecs) (G : @funspecs Σ) {C : compspecs},
  Genv.t fundef type → coPset → list (ident * fundef) → @funspecs Σ → Prop.

Parameter semax_external: forall {Σ : gFunctors} {heapGS0 : heapGS Σ} {Espec : OracleKind}
  `{!externalGS (OK_ty(Σ := Σ)) Σ}, coPset → external_function →
  ∀ A : Type, (A → @argsassert Σ) → (A → @assert Σ) → mpred.

End CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module DerivedDefs (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF).

Definition semax_body `{!heapGS Σ} {Espec} `{!externalGS OK_ty Σ}
   (V: varspecs) (G: funspecs) {C: compspecs} E (f: function) (spec: ident * funspec): Prop :=
match spec with (_, mk_funspec fsig cc A P Q) =>
  fst fsig = map snd (fst (fn_funsig f)) /\
  snd fsig = snd (fn_funsig f) /\
forall (x:A),
  Def.semax E (func_tycontext f V G nil)
      (close_precondition (map fst f.(fn_params)) (P x) ∗ stackframe_of f)
       f.(fn_body)
      (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f))
end.

Definition semax_prog `{!heapGS Σ} {Espec} `{!externalGS OK_ty Σ} {C: compspecs}
       (prog: program) (ora: OK_ty) (V: varspecs) (G: funspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
Maps.PTree.elements cenv_cs = Maps.PTree.elements (prog_comp_env prog) /\
Def.semax_func V G (Genv.globalenv prog) ⊤ (prog_funct prog) G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post,
      s = main_spec_ext' prog ora post
| None => False
end.

End DerivedDefs.

Module Type MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module CSHL_Defs := DerivedDefs(CSHL_Def).

Import CSHL_Def.
Import CSHL_Defs.

(***************** SEMAX_LEMMAS ****************)

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (OK_ty(Σ := Σ)) Σ} {CS: compspecs}.

Axiom semax_extract_exists:
  forall E (A : Type) (P : A -> assert) c (Delta: tycontext) (R: ret_assert),
  (forall x, semax E Delta (P x) c R) ->
   semax E Delta (∃ x:A, P x) c R.

Axiom semax_func_nil:
        forall V G ge E, semax_func V G ge E nil nil.

Axiom semax_func_cons:
     forall fs id f fsig cc A P Q (V: varspecs) (G G': funspecs) ge E b,
  andb (id_in_list id (map (@fst _ _) G))
  (andb (negb (id_in_list id (map (@fst ident Clight.fundef) fs)))
    (semax_body_params_ok f)) = true ->
  Forall
     (fun it : ident * type =>
      complete_type cenv_cs (snd it) =
      true) (fn_vars f) ->
   var_sizes_ok cenv_cs (f.(fn_vars)) ->
   f.(fn_callconv) = cc ->
   Genv.find_symbol ge id = Some b -> 
   Genv.find_funct_ptr ge b = Some (Internal f) -> 
  semax_body V G E f (id, mk_funspec fsig cc A P Q) ->
  semax_func V G ge E fs G' ->
  semax_func V G ge E ((id, Internal f)::fs)
       ((id, mk_funspec fsig cc A P Q)  :: G').

Axiom semax_func_cons_ext: forall (V: varspecs) (G: funspecs) 
     {C: compspecs} ge E fs id ef argsig retsig A (P: A -> argsassert) (Q: A -> assert) argsig'
      (G': funspecs) cc b,
  argsig' = typelist2list argsig ->
  ef_sig ef = mksignature (typlist_of_typelist argsig) (rettype_of_type retsig) cc ->
  id_in_list id (map (@fst _ _) fs) = false ->
  (ef_inline ef = false \/ withtype_empty A) ->
  (forall gx x (ret : option val),
     (Q x (make_ext_rval gx (rettype_of_type retsig) ret)
        ∧ ⌜Builtins0.val_opt_has_rettype ret (rettype_of_type retsig)⌝
        ⊢ ⌜tc_option_val retsig ret⌝)) ->
  Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
  (⊢semax_external E ef A P Q) ->
  semax_func V G ge E fs G' ->
  semax_func V G ge E ((id, External ef argsig retsig cc)::fs)
       ((id, mk_funspec (argsig', retsig) cc A P Q)  :: G').

Axiom semax_func_mono: forall {CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G E fdecs G1 (H: semax_func V G (C := CS) ge E fdecs G1), semax_func V G (C := CS') ge' E fdecs G1.

Axiom semax_func_app:
  forall ge E V H funs1 funs2 G1 G2
         (SF1: semax_func V H ge E funs1 G1) (SF2: semax_func V H ge E funs2 G2)
         (L:length funs1 = length G1),
    semax_func V H ge E (funs1 ++ funs2) (G1++G2).
  
Axiom semax_func_subsumption:
  forall ge E V V' F F'
         (SUB: tycontext_sub E (nofunc_tycontext V F) (nofunc_tycontext V F'))
         (HV: forall id, sub_option ((make_tycontext_g V F) !! id) ((make_tycontext_g V' F') !! id)),
  forall funs G (SF: semax_func V F ge E funs G),  semax_func V' F' ge E funs G.
  
Axiom semax_func_join:
  forall {ge E V1 H1 V2 H2 V funs1 funs2 G1 G2 H}
  (SF1: semax_func V1 H1 ge E funs1 G1) (SF2: semax_func V2 H2 ge E funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_g V1 H1) !! i) ((make_tycontext_g V1 H) !! i))
  (K2: forall i, subsumespec E ((make_tycontext_s H1) !! i) ((make_tycontext_s H) !! i))
  (K3: forall i, sub_option ((make_tycontext_g V1 H) !! i) ((make_tycontext_g V H) !! i))

  (N1: forall i, sub_option ((make_tycontext_g V2 H2) !! i) ((make_tycontext_g V2 H) !! i))
  (N2: forall i, subsumespec E ((make_tycontext_s H2) !! i) ((make_tycontext_s H) !! i))
  (N3: forall i, sub_option ((make_tycontext_g V2 H) !! i) ((make_tycontext_g V H) !! i)),
semax_func V H ge E (funs1 ++ funs2) (G1++G2).

Axiom semax_func_firstn:
  forall {ge E H V n funs G} (SF: semax_func V H ge E funs G),
    semax_func V H ge E (firstn n funs) (firstn n G).

Axiom semax_func_skipn:
  forall {ge E H V funs G} (HV: list_norepet (map fst funs)) (SF: semax_func V H ge E funs G) n,
    semax_func V H ge E (skipn n funs) (skipn n G).

Axiom semax_body_subsumption: forall E V V' F F' f spec
      (SF: semax_body V F E f spec)
      (TS: tycontext_sub E (func_tycontext f V F nil) (func_tycontext f V' F' nil)),
  semax_body V' F' E f spec.
  
Axiom semax_body_cenv_sub: forall {CS'} (CSUB: cspecs_sub CS CS') V G E f spec
      (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)),
  semax_body V G (C := CS) E f spec -> semax_body V G (C := CS') E f spec.

(* THESE RULES FROM semax_loop *)

Axiom semax_ifthenelse :
   forall E Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax E Delta (P ∧ local (expr_true b)) c R ->
     semax E Delta (P ∧ local (expr_false b)) d R ->
     semax E Delta (▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P)) (Sifthenelse b c d) R.

Axiom semax_seq:
  forall E Delta (R: ret_assert) P Q h t,
  semax E Delta P h (overridePost Q R) ->
  semax E Delta Q t R ->
  semax E Delta P (Clight.Ssequence h t) R.

Axiom semax_break:
   forall E Delta Q,    semax E Delta (RA_break Q) Sbreak Q.

Axiom semax_continue:
   forall E Delta Q,    semax E Delta (RA_continue Q) Scontinue Q.

Axiom semax_loop :
forall E Delta (Q Q' : assert) incr body R,
     semax E Delta Q body (loop1_ret_assert Q' R) ->
     semax E Delta Q' incr (loop2_ret_assert Q R) ->
     semax E Delta Q (Sloop body incr) R.

(* THIS RULE FROM semax_switch *)

Axiom semax_switch: 
  forall E Delta (Q: assert) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho ⊢ tc_expr Delta a rho) ->
     (forall n,
     semax E Delta 
               (local (`eq (eval_expr a) `(Vint n)) ∧ Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     semax E Delta Q (Sswitch a sl) R.

(* THESE RULES FROM semax_call *)

Axiom semax_call:
  forall E Delta (A: Type) P Q x
   F ret id argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax E Delta
          ((tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
         (assert_of (fun rho => func_ptr (ge_of rho) E id (mk_funspec (argsig,retsig) cc A P Q) (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).

Axiom  semax_return :
   forall E Delta (R: ret_assert) ret,
      semax E Delta
                (tc_expropt Delta ret (ret_type Delta) ∧
                (assert_of (`(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))))
                (Sreturn ret)
                R.

(* THESE RULES FROM semax_straight *)

Axiom semax_set_forward :
forall E (Delta: tycontext) (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
          P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) ∧
                            assert_of (subst id (`old) P))).

Axiom semax_ptr_compare :
forall E (Delta: tycontext) P id cmp e1 e2 ty sh1 sh2,
   sh1 <> Share.bot -> sh2 <> Share.bot ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   semax E Delta
        ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          <absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)) ∧
          <absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2)) ∧
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (∃ old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) ∧
                            assert_of (subst id `(old) P))).

Axiom semax_load :
forall E (Delta: tycontext) sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax E Delta
       (▷ ( (tc_lvalue Delta e1) ∧
       local (`(tc_val (typeof e1) v2)) ∧
          P))
       (Sset id e1)
       (normal_ret_assert (∃ old:val, local (`eq (eval_id id) (`v2)) ∧
                                          assert_of (subst id (`old) P))).

Axiom semax_cast_load :
forall E (Delta: tycontext) sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax E Delta
       (▷ ( (tc_lvalue Delta e1) ∧
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (∃ old:val, local (`eq (eval_id id) (`(eval_cast (typeof e1) t1 v2))) ∧
                                          assert_of (subst id (`old) P))).

Axiom semax_store:
 forall E Delta e1 e2 sh P,
   writable_share sh ->
   semax E Delta
          (▷ ( (tc_lvalue Delta e1) ∧  (tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ P)))
          (Sassign e1 e2)
          (normal_ret_assert
               (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) ∗ P)).

Axiom semax_store_union_hack:
     forall E (Delta : tycontext) (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : assert),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax E Delta
         (▷ (tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)) ∧
              ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1)))
               ∗ P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (∃ v':val,
              (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) ∧
              (assert_of ((` (mapsto sh t2)) (eval_lvalue e1) (`v')) ∗ P))).

(* THESE RULES FROM semax_lemmas *)

Axiom semax_skip:
   forall E Delta (P : assert), semax E Delta P Sskip (normal_ret_assert P).

Axiom semax_conseq:
  forall E Delta (P' : assert) (R': ret_assert) P c (R: ret_assert),
    (local (tc_environ Delta) ∧ ((allp_fun_id E Delta) ∧ P) ⊢ (|={E}=> P')) ->
    (local (tc_environ Delta) ∧ ((allp_fun_id E Delta) ∧ RA_normal R') ⊢ (|={E}=> RA_normal R)) ->
    (local (tc_environ Delta) ∧ ((allp_fun_id E Delta) ∧ RA_break R') ⊢ (|={E}=> RA_break R)) ->
    (local (tc_environ Delta) ∧ ((allp_fun_id E Delta) ∧ RA_continue R') ⊢ (|={E}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) ∧ ((allp_fun_id E Delta) ∧ RA_return R' vl) ⊢ (RA_return R vl)) ->
   semax E Delta P' c R' -> semax E Delta P c R.

Axiom semax_Slabel:
     forall E Delta (P:assert) (c:statement) (Q:ret_assert) l,
   semax E Delta P c Q -> semax E Delta P (Slabel l c) Q.

(* THESE RULES FROM semax_ext *)

(*TODO: What's the preferred way to expose these defs in the SL interface?*)
Axiom semax_ext:
  forall E (ext_link: Strings.String.string -> ident)
         (id : Strings.String.string) (sig : typesig) (sig' : signature)
         cc A P Q (fs : funspecs),
  let f := mk_funspec sig cc A P Q in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  sig' = semax_ext.typesig2signature sig cc ->
  ⊢ semax_external (Espec := {| OK_ty := OK_ty; OK_spec := add_funspecs_rec OK_ty ext_link OK_spec fs |} ) E (EF_external id sig') _ P Q.

Axiom semax_external_FF:
 forall E ef A,
 ⊢ semax_external E ef A (fun _ => False) (fun _ => False).

Axiom semax_external_binaryintersection: 
forall {E ef A1 P1 Q1 A2 P2 Q2
      A P Q sig cc}
  (EXT1: ⊢ semax_external E ef A1 P1 Q1)
  (EXT2: ⊢ semax_external E ef A2 P2 Q2)
  (BI: binary_intersection (mk_funspec sig cc A1 P1 Q1)
                      (mk_funspec sig cc A2 P2 Q2) =
     Some (mk_funspec sig cc A P Q))
  (LENef: length (fst sig) = length (sig_args (ef_sig ef))),
  ⊢ semax_external E ef A P Q.

Axiom semax_external_funspec_sub: forall 
  {E argtypes rtype cc ef A1 P1 Q1 A P Q}
  (Hsub: funspec_sub E (mk_funspec (argtypes, rtype) cc A1 P1 Q1)
                   (mk_funspec (argtypes, rtype) cc A P Q))
  (HSIG: ef_sig ef = 
         mksignature (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc),
  semax_external E ef A1 P1 Q1 ⊢ semax_external E ef A P Q.

Axiom semax_body_binaryintersection:
forall {V G} E f sp1 sp2 phi
  (SB1: semax_body V G E f sp1) (SB2: semax_body V G E f sp2)
  (BI: binary_intersection (snd sp1) (snd sp2) = Some phi),
  semax_body V G E f (fst sp1, phi).

Axiom semax_body_funspec_sub: forall {V G E f i phi phi'} 
  (SB: semax_body V G E f (i, phi)) (Sub: funspec_sub E phi phi')
  (LNR: list_norepet (map fst (fn_params f) ++ map fst (fn_temps f))),
  semax_body V G E f (i, phi').

Axiom semax_Delta_subsumption:
  forall E Delta Delta' P c R,
       tycontext_sub E Delta Delta' ->
       semax E Delta P c R -> semax E Delta' P c R.

End mpred.

End MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Module Type PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.

Declare Module CSHL_MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Import CSHL_MinimumLogic.CSHL_Def.
Import CSHL_MinimumLogic.CSHL_Defs.

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (OK_ty(Σ := Σ)) Σ} {CS: compspecs}.

Axiom semax_set :
forall E (Delta: tycontext) (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P)))
          (Sset id e) (normal_ret_assert P).

Axiom semax_fun_id:
      forall id f E Delta P Q c,
    (var_types Delta) !! id = None ->
    (glob_specs Delta) !! id = Some f ->
    (glob_types Delta) !! id = Some (type_of_funspec f) ->
    semax E Delta (P ∧ assert_of (fun rho => func_ptr (ge_of rho) E id f (eval_var id (type_of_funspec f) rho)))
                  c Q ->
    semax E Delta P c Q.

Axiom semax_unfold_Ssequence: forall c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q E Delta, semax E Delta P c1 Q -> semax E Delta P c2 Q).

Axiom seq_assoc:
   forall E Delta P s1 s2 s3 R,
        semax E Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        semax E Delta P (Ssequence (Ssequence s1 s2) s3) R.

Axiom semax_seq_skip:
  forall E Delta P s Q,
    semax E Delta P s Q <-> semax E Delta P (Ssequence s Sskip) Q.

Axiom semax_skip_seq:
  forall E Delta P s Q,
    semax E Delta P s Q <-> semax E Delta P (Ssequence Sskip s) Q.

Axiom semax_loop_nocontinue1:
  forall E Delta Pre s1 s2 s3 Post,
  nocontinue s1 = true ->
  nocontinue s2 = true ->
  nocontinue s3 = true ->
   semax E Delta Pre (Sloop (Ssequence s1 (Ssequence s2 s3)) Sskip) Post ->
    semax E Delta Pre (Sloop (Ssequence s1 s2) s3) Post.

Axiom semax_loop_nocontinue:
 forall E Delta P body incr R,
 semax E Delta P (Ssequence body incr) (loop_nocontinue_ret_assert P R) ->
 semax E Delta P (Sloop body incr) R.

Axiom semax_convert_for_while':
 forall E Delta Pre s1 e2 s3 s4 s5 Post,
  nocontinue s4 = true ->
  nocontinue s3 = true -> 
  semax E Delta Pre 
    (Ssequence s1 (Ssequence (Swhile e2 (Ssequence s4 s3)) s5)) Post ->
  semax E Delta Pre (Ssequence (Sfor s1 e2 s4 s3) s5) Post.

Axiom semax_loop_unroll1:
  forall E Delta P P' Q body incr R,
  semax E Delta P body (loop1_ret_assert P' R) ->
  semax E Delta P' incr (loop2_ret_assert Q R) ->
  semax E Delta Q (Sloop body incr) R ->
  semax E Delta P (Sloop body incr) R.

Axiom semax_if_seq:
 forall E Delta P e c1 c2 c Q,
 semax E Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax E Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.

Axiom semax_seq_Slabel:
     forall E Delta (P:assert) (c1 c2:statement) (Q:ret_assert) l,
   semax E Delta P (Ssequence (Slabel l c1) c2) Q <-> 
   semax E Delta P (Slabel l (Ssequence c1 c2)) Q.

(**************** END OF stuff from semax_rules ***********)

Axiom semax_frame:
  forall E Delta (P : assert) s R (F : assert),
   closed_wrt_modvars s F ->
  semax E Delta P s R ->
    semax E Delta (P ∗ F) s (frame_ret_assert R F).

Axiom semax_extract_prop:
  forall E Delta (PP: Prop) (P : assert) c Q,
           (PP -> semax E Delta P c Q) ->
           semax E Delta (⌜PP⌝ ∧ P) c Q.

Axiom semax_extract_later_prop:
  forall E Delta (PP: Prop) (P : assert) c Q,
           (PP -> semax E Delta P c Q) ->
           semax E Delta ((▷ ⌜PP⌝) ∧ P) c Q.

Axiom semax_adapt_frame: forall E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   ∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ |={E}=> (P' rho ∗ F rho) ∧
                         ⌜forall rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_normal (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_normal Q rho)⌝ ∧
                         ⌜forall rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_break (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_break Q rho)⌝ ∧
                         ⌜forall rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_continue (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_continue Q rho)⌝ ∧
                         ⌜forall vl rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_return (frame_ret_assert Q' F) vl rho ⊢ RA_return Q vl rho)⌝))
   (SEM: semax E Delta P' c Q'),
   semax E Delta P c Q.

Axiom semax_adapt: forall E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   (|={E}=> (P' rho) ∧
                        ⌜forall rho, RA_normal Q' rho ⊢ |={E}=> RA_normal Q rho⌝ ∧
                        ⌜forall rho, RA_break Q' rho ⊢ |={E}=> RA_break Q rho⌝ ∧
                        ⌜forall rho, RA_continue Q' rho ⊢ |={E}=> RA_continue Q rho⌝ ∧
                        ⌜forall vl rho, RA_return Q' vl rho ⊢ RA_return Q vl rho⌝))
   (SEM: semax E Delta P' c Q'),
   semax E Delta P c Q.

End mpred.

End PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.
