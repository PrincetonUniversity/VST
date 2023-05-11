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
Require Export VST.veric.Clight_lemmas.
Require Export VST.veric.composite_compute.
Require Export VST.veric.align_mem.
Require Export VST.veric.shares.
Require Export VST.veric.seplog.
Require Export VST.veric.Clight_seplog.
Require Export VST.veric.Clight_assert_lemmas.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.valid_pointer.
Require Export VST.veric.semax_prog.
Require Export VST.veric.semax_ext.
Import LiftNotation.
Import Ctypes Clight expr.

#[export] Existing Instance EqDec_ident.
#[export] Existing Instance EqDec_byte.
#[export] Existing Instance EqDec_memval.
#[export] Existing Instance EqDec_quantity.

Definition local:  (environ -> Prop) -> environ->mpred :=  lift1 prop.

Global Opaque mpred.

#[export] Hint Resolve any_environ : typeclass_instances.

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
Definition func_ptr (f: funspec) (v: val): mpred := seplog.func_ptr_si f v.

(*veric.seplog has a lemma that weakens the hypothesis here to funspec_sub_si*)
Lemma func_ptr_mono fs gs v (H:funspec_sub fs gs): func_ptr fs v |-- func_ptr gs v.
Proof. constructor; apply funspec_sub_implies_func_prt_si_mono.
       now rewrite <- funspec_sub_iff.
Qed.

Lemma func_ptr_isptr: forall spec f, func_ptr spec f |-- !! isptr f.
Proof. constructor; apply seplog.func_ptr_si_isptr.
Qed.

Definition type_of_funsig (fsig: funsig) :=
   Tfunction (type_of_params (fst fsig)) (snd fsig) cc_default.

Definition with_ge (ge: genviron) (G: environ->mpred) : mpred :=
     G (mkEnviron ge (Map.empty _) (Map.empty _)).

Fixpoint arglist (n: positive) (tl: typelist) : list (ident*type) :=
 match tl with
  | Tnil => nil
  | Tcons t tl' => (n,t):: arglist (n+1)%positive tl'
 end.

Definition  funspecs_norepeat (fs : funspecs) := list_norepet (map fst fs).

(* Misc lemmas *)
Lemma typecheck_lvalue_sound {CS: compspecs} :
  forall Delta rho e,
    typecheck_environ Delta rho ->
    tc_lvalue Delta e rho |-- !! is_pointer_or_null (eval_lvalue e rho).
Proof.
constructor; intros.
intros ? ?.
eapply expr_lemmas4.typecheck_lvalue_sound; eauto.
Qed.

Lemma typecheck_expr_sound {CS: compspecs} :
  forall Delta rho e,
    typecheck_environ Delta rho ->
    tc_expr Delta e rho |-- !! tc_val (typeof e) (eval_expr e rho).
Proof.
constructor; intros.
intros ? ?.
simpl.
eapply expr_lemmas4.typecheck_expr_sound; eauto.
Qed.

(***************LENB: ADDED THESE LEMMAS IN INTERFACE************************************)

Lemma tc_expr_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  @tc_expr CS Delta e rho |-- @tc_expr CS' Delta e rho.
Proof. intros. destruct CSUB as [CSUB _]. rewrite tc_expr_eq. constructor; intros w W. apply (extend_tc.tc_expr_cenv_sub CSUB e rho Delta). trivial. Qed.

Lemma tc_expropt_char {CS} Delta e t: @tc_expropt CS Delta e t =
                                      match e with None => `!!(t=Tvoid)
                                              | Some e' => @tc_expr CS Delta (Ecast e' t)
                                      end.
Proof. reflexivity. Qed.

Lemma tc_expropt_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- @tc_expropt CS' Delta ret t rho.
Proof.
  destruct ret; simpl. 2: constructor; apply  predicates_hered.derives_refl.
  apply (tc_expr_cspecs_sub CSUB Delta (Ecast e t) rho D). 
Qed.

Lemma tc_lvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  @tc_lvalue CS Delta e rho |-- @tc_lvalue CS' Delta e rho.
Proof. intros; simpl. destruct CSUB as [CSUB _]. constructor; red; intros. apply (extend_tc.tc_lvalue_cenv_sub CSUB e rho Delta). apply H0. Qed.

Lemma tc_exprlist_cspecs_sub {CS CS'} (CSUB: cspecs_sub  CS CS') Delta rho: forall types e,
  tc_environ Delta rho ->
  @tc_exprlist CS Delta types e rho |-- @tc_exprlist CS' Delta types e rho.
Proof. intros. destruct CSUB as [CSUB _]. constructor; intros w W. apply (extend_tc.tc_exprlist_cenv_sub CSUB Delta rho w types e W). Qed.

Lemma eval_exprlist_cspecs_sub {CS CS'} (CSUB: cspecs_sub  CS CS') Delta rho (TCD: tc_environ Delta rho):
  forall types e,
  @tc_exprlist CS Delta types e rho |-- !! (@eval_exprlist CS types e rho = @eval_exprlist CS' types e rho).
Proof. intros. destruct CSUB as [CSUB _]. constructor; intros w W. eapply (expr_lemmas.typecheck_exprlist_sound_cenv_sub CSUB); eassumption. Qed.

Lemma denote_tc_assert_tc_bool_cs_invariant {CS CS'} b E:
  @denote_tc_assert CS (tc_bool b E) = @denote_tc_assert CS' (tc_bool b E).
Proof. unfold tc_bool. destruct b; reflexivity. Qed.

Lemma tc_temp_id_cspecs_sub {CS CS'} (CSUB: cspecs_sub  CS CS') Delta rho e i:
  tc_environ Delta rho -> @tc_temp_id i (typeof e) CS Delta e rho |-- @tc_temp_id i (typeof e) CS' Delta e rho.
Proof.
  intros. constructor; unfold tc_temp_id, typecheck_temp_id; intros w W.
  destruct ((temp_types Delta)! i); [| apply W].
  rewrite denote_tc_assert_andp in W.
  rewrite denote_tc_assert_andp; destruct W as [W1 W2];  split.
+ rewrite (@denote_tc_assert_tc_bool_cs_invariant CS' CS). exact W1. 
+ apply expr2.tc_bool_e in W1. eapply expr2.neutral_isCastResultType.
  exact W1.
Qed. 

(*Proof exists in semax_call under name RA_return_castexpropt_cenv_sub -- repeat here for the exposed def of castexprof?*)
Lemma castexpropt_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') Delta rho (D:typecheck_environ Delta rho) ret t:
  @tc_expropt CS Delta ret t rho |-- !!(@cast_expropt CS ret t rho = @cast_expropt CS' ret t rho).
Proof.
  constructor; intros w W. destruct CSUB as [CSUB _]. rewrite tc_expropt_char in W. destruct ret; [ | reflexivity].
  specialize (expr_lemmas.typecheck_expr_sound_cenv_sub CSUB Delta rho D w (Ecast e t) W); clear W; intros H.
  hnf. unfold cast_expropt. simpl; simpl in H. 
  unfold force_val1, force_val, sem_cast, liftx, lift; simpl.
  unfold force_val1, force_val, sem_cast, liftx, lift in H; simpl in H. rewrite H; trivial.
Qed.

Lemma RA_return_cast_expropt_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e t R rho,
  tc_environ Delta rho ->
  @tc_expropt CS Delta e t rho && RA_return R (@cast_expropt CS e t rho) (id rho)
  |-- RA_return R (@cast_expropt CS' e t rho) (id rho).
Proof.
  intros. constructor; intros w [W1 W2].
  pose proof (castexpropt_cenv_sub CSUB _ _ H e t) as H1. unseal_derives.
  rewrite (H1 w W1) in W2. apply W2.
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

Definition withtype_empty (A: rmaps.TypeTree) : Prop :=
  forall ts : list Type,
 functors.MixVariantFunctor._functor
   (rmaps.dependent_type_functor_rec ts A)
   (predicates_hered.pred compcert_rmaps.RML.R.rmap) -> False.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Parameter semax: forall {CS: compspecs} {Espec: OracleKind},
    tycontext -> (environ->mpred) -> statement -> ret_assert -> Prop.

Parameter semax_func:
    forall {Espec: OracleKind},
    forall (V: varspecs) (G: funspecs) {C: compspecs} (ge: Genv.t fundef type) (fdecs: list (ident * fundef)) (G1: funspecs), Prop.

Parameter semax_external: forall {Hspec: OracleKind} (ef: external_function) (A : rmaps.TypeTree)
       (P: forall ts : list Type, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (ArgsTT A)) mpred)
       (Q: forall ts : list Type, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred), Prop.

End CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module DerivedDefs (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF).

Local Open Scope pred.

Definition semax_body
   (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=
match spec with (_, mk_funspec fsig cc A P Q _ _) =>
  fst fsig = map snd (fst (fn_funsig f)) /\ 
  snd fsig = snd (fn_funsig f) /\
forall Espec ts x,
  @Def.semax C Espec (func_tycontext f V G nil)
      (fun rho => close_precondition (map fst f.(fn_params)) (P ts x) rho * stackframe_of f rho)
       f.(fn_body)
      (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))
end.

Definition semax_prog {Espec: OracleKind}{C: compspecs}
       (prog: program) (z: OK_ty) (V: varspecs) (G: funspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
PTree.elements cenv_cs = PTree.elements (prog_comp_env prog) /\
  @Def.semax_func Espec V G C (Genv.globalenv prog)  (prog_funct prog) G /\
  match_globvars (prog_vars prog) V = true /\
  match initial_world.find_id prog.(prog_main) G with
  | Some s => exists post,
             s = main_spec_ext' prog z post
  | None => False
end.

End DerivedDefs.

Module Type MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module CSHL_Defs := DerivedDefs(CSHL_Def).

Import CSHL_Def.
Import CSHL_Defs.

(***************** SEMAX_LEMMAS ****************)

Axiom semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type) (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.
  
Axiom semax_func_nil:   forall {Espec: OracleKind},
        forall V G C ge, @semax_func Espec V G C ge nil nil.

Axiom semax_func_cons:
  forall {Espec: OracleKind},
     forall fs id f fsig cc A P Q NEP NEQ (V: varspecs) (G G': funspecs) {C: compspecs} ge b,
  andb (id_in_list id (map (@fst _ _) G))
  (andb (negb (id_in_list id (map (@fst ident Clight.fundef) fs)))
    (semax_body_params_ok f)) = true ->
  Forall
     (fun it : ident * type =>
      complete_type cenv_cs (snd it) =
      true) (fn_vars f) ->
   var_sizes_ok (f.(fn_vars)) ->
   f.(fn_callconv) = cc ->
   Genv.find_symbol ge id = Some b -> 
   Genv.find_funct_ptr ge b = Some (Internal f) -> 
  semax_body V G f (id, mk_funspec fsig cc A P Q NEP NEQ) ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, Internal f)::fs)
       ((id, mk_funspec fsig cc A P Q NEP NEQ)  :: G').

Axiom semax_func_cons_ext: forall {Espec:OracleKind} (V: varspecs) (G: funspecs) 
     {C: compspecs} ge fs id ef argsig retsig A P Q NEP NEQ argsig'
      (G': funspecs) cc b,
  argsig' = typelist2list argsig ->
  ef_sig ef = mksignature (typlist_of_typelist argsig) (rettype_of_type retsig) cc ->
  id_in_list id (map (@fst _ _) fs) = false ->
  (ef_inline ef = false \/ withtype_empty A) ->
  (forall gx ts x (ret : option val),
     (Q ts x (make_ext_rval gx (rettype_of_type retsig) ret)
        && !!Builtins0.val_opt_has_rettype ret (rettype_of_type retsig)
        |-- !!tc_option_val retsig ret)) ->
  Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
  @semax_external Espec ef A P Q ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, External ef argsig retsig cc)::fs)
       ((id, mk_funspec (argsig', retsig) cc A P Q NEP NEQ)  :: G').

Axiom semax_func_mono: forall  {Espec CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G fdecs G1 (H: @semax_func Espec V G CS ge fdecs G1), @semax_func Espec V G CS' ge' fdecs G1.

Axiom semax_func_app:
  forall Espec ge cs V H funs1 funs2 G1 G2
         (SF1: @semax_func Espec V H cs ge funs1 G1) (SF2: @semax_func Espec V H cs ge funs2 G2)
         (L:length funs1 = length G1),
    @semax_func Espec V H cs ge (funs1 ++ funs2) (G1++G2).
  
Axiom semax_func_subsumption:
  forall Espec ge cs V V' F F'
         (SUB: tycontext_sub (nofunc_tycontext V F) (nofunc_tycontext V F'))
         (HV: forall id, sub_option (make_tycontext_g V F) ! id (make_tycontext_g V' F') ! id),
  forall funs G (SF: @semax_func Espec V F cs ge funs G),  @semax_func Espec V' F' cs ge funs G.
  
Axiom semax_func_join:
  forall {Espec cs ge V1 H1 V2 H2 V funs1 funs2 G1 G2 H}
  (SF1: @semax_func Espec V1 H1 cs ge funs1 G1) (SF2: @semax_func Espec V2 H2 cs ge funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_g V1 H1) ! i) ((make_tycontext_g V1 H) ! i))
  (K2: forall i, subsumespec ((make_tycontext_s H1) ! i) ((make_tycontext_s H) ! i))
  (K3: forall i, sub_option ((make_tycontext_g V1 H) ! i) ((make_tycontext_g V H) ! i))

  (N1: forall i, sub_option ((make_tycontext_g V2 H2) ! i) ((make_tycontext_g V2 H) ! i))
  (N2: forall i, subsumespec ((make_tycontext_s H2) ! i) ((make_tycontext_s H) ! i))
  (N3: forall i, sub_option ((make_tycontext_g V2 H) ! i) ((make_tycontext_g V H) ! i)),
  @semax_func Espec V H cs ge (funs1 ++ funs2) (G1++G2).
  
Axiom semax_func_firstn:
  forall {Espec cs ge H V n funs G} (SF: @semax_func Espec V H cs ge funs G),
    @semax_func Espec V H cs ge (firstn n funs) (firstn n G).
  
Axiom semax_func_skipn:
  forall {Espec cs ge H V funs G} (HV:list_norepet (map fst funs))
         (SF: @semax_func Espec V H cs ge funs G) n,
    @semax_func Espec V H cs ge (skipn n funs) (skipn n G).

Axiom semax_body_subsumption: forall cs V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)),
  @semax_body V' F' cs f spec.
  
Axiom semax_body_cenv_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS') V G f spec
      (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)),
  @semax_body V G CS f spec -> @semax_body V G CS' f spec.

(* THESE RULES FROM semax_loop *)

Axiom semax_ifthenelse :
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (|> (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P)) (Sifthenelse b c d) R.

Axiom semax_seq:
  forall{CS: compspecs} {Espec: OracleKind},
forall Delta R P Q h t,
    @semax CS Espec Delta P h (overridePost Q R) ->
    @semax CS Espec Delta Q t R ->
    @semax CS Espec Delta P (Ssequence h t) R.

Axiom semax_break:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta Q,    @semax CS Espec Delta (RA_break Q) Sbreak Q.

Axiom semax_continue:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta Q,    @semax CS Espec Delta (RA_continue Q) Scontinue Q.

Axiom semax_loop :
  forall{CS: compspecs} {Espec: OracleKind},
forall Delta Q Q' incr body R,
     @semax CS Espec Delta  Q body (loop1_ret_assert Q' R) ->
     @semax CS Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax CS Espec Delta Q (Sloop body incr) R.

(* THIS RULE FROM semax_switch *)

Axiom semax_switch: 
  forall{CS: compspecs} {Espec: OracleKind},
  forall Delta (Q: environ->mpred) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta Q (Sswitch a sl) R.

(* THESE RULES FROM semax_call *)

Axiom semax_call: forall {CS Espec},
  forall Delta (A: rmaps.TypeTree) P Q
  (NEP: args_super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) x
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((((tc_expr Delta a) && (tc_exprlist Delta argsig bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          (|>(F * (fun rho => P ts x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).

Axiom  semax_return :
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R.

(* THESE RULES FROM semax_straight *)

Axiom semax_set_forward :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).

Axiom semax_ptr_compare :
forall{CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                            subst id `(old) P)).

Axiom semax_load :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (`v2)) &&
                                          (subst id (`old) P))).

Axiom semax_cast_load :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (`(eval_cast (typeof e1) t1 v2))) &&
                                          (subst id (`old) P))).

Axiom semax_store:
  forall {CS: compspecs} {Espec: OracleKind},
 forall Delta e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
               (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).

Axiom semax_store_union_hack:
     forall {cs: compspecs} {Espec:OracleKind}
          (Delta : tycontext) (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : LiftEnviron mpred),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax Delta
         (|> (tc_lvalue Delta e1 && tc_expr Delta (Ecast e2 (typeof e1)) &&
              ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1) 
                && `(mapsto_ sh t2) (eval_lvalue e1))
               * P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (EX v':val, 
              andp (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') ))
              ((` (mapsto sh t2)) (eval_lvalue e1) (`v') * P))).

(* THESE RULES FROM semax_lemmas *)

Axiom semax_skip:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P, @semax CS Espec Delta P Sskip (normal_ret_assert P).

Axiom semax_conseq:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (P' : environ -> mpred) (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- (|={Ensembles.Full_set}=> P')) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- (|={Ensembles.Full_set}=> RA_normal R)) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- (|={Ensembles.Full_set}=> RA_break R)) ->
    (local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- (|={Ensembles.Full_set}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- (RA_return R vl)) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

Axiom semax_Slabel:
   forall {cs:compspecs} {Espec: OracleKind},
     forall Delta (P:environ -> mpred) (c:statement) (Q:ret_assert) l,
   @semax cs Espec Delta P c Q -> @semax cs Espec Delta P (Slabel l c) Q.

(* THESE RULES FROM semax_ext *)

(*TODO: What's the preferred way to expose these defs in the SL interface?*)
Axiom semax_ext:
  forall  (Espec : OracleKind)
         (ext_link: Strings.String.string -> ident)
         (id : Strings.String.string) (sig : compcert_rmaps.typesig) (sig' : signature)
         cc A P Q NEP NEQ (fs : funspecs),
  let f := mk_funspec sig cc A P Q NEP NEQ in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  sig' = semax_ext.typesig2signature sig cc ->
  @semax_external (add_funspecs Espec ext_link fs) (EF_external id sig') _ P Q.

Axiom semax_external_FF:
 forall Espec ef A,
  @semax_external Espec ef A (fun _ _ => FF) (fun _ _ => FF).

Axiom semax_external_binaryintersection: 
forall {Espec ef A1 P1 Q1 P1ne Q1ne A2 P2 Q2 P2ne Q2ne 
      A P Q P_ne Q_ne sig cc}
  (EXT1: @semax_external Espec ef A1 P1 Q1)
  (EXT2: @semax_external Espec ef A2 P2 Q2)
  (BI: binary_intersection (mk_funspec sig cc A1 P1 Q1 P1ne Q1ne) 
                      (mk_funspec sig cc A2 P2 Q2 P2ne Q2ne) =
     Some (mk_funspec sig cc A P Q P_ne Q_ne))
  (LENef: length (fst sig) = length (sig_args (ef_sig ef))),
  @semax_external Espec ef A P Q.

Axiom semax_external_funspec_sub: forall 
  (DISABLE: False) {Espec argtypes rtype cc ef A1 P1 Q1 P1ne Q1ne A P Q Pne Qne}
  (Hsub: funspec_sub (mk_funspec (argtypes, rtype) cc A1 P1 Q1 P1ne Q1ne) 
                   (mk_funspec (argtypes, rtype) cc A P Q Pne Qne))
  (HSIG: ef_sig ef = 
         mksignature (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc)
  (SE: @semax_external Espec ef A1 P1 Q1),
  @semax_external Espec ef A P Q.

Axiom semax_body_binaryintersection:
forall {V G cs} f sp1 sp2 phi
  (SB1: @semax_body V G cs f sp1) (SB2: @semax_body V G cs f sp2)
  (BI: binary_intersection (snd sp1) (snd sp2) = Some phi),
  @semax_body V G cs f (fst sp1, phi).

Axiom semax_body_funspec_sub: forall {V G cs f i phi phi'} 
  (SB: @semax_body V G cs f (i, phi)) (Sub: funspec_sub phi phi')
  (LNR: list_norepet (map fst (fn_params f) ++ map fst (fn_temps f))),
  @semax_body V G cs f (i, phi').

Axiom semax_Delta_subsumption:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
       @semax CS Espec Delta P c R -> @semax CS Espec Delta' P c R.

End MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Module Type PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.

Declare Module CSHL_MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Import CSHL_MinimumLogic.CSHL_Def.
Import CSHL_MinimumLogic.CSHL_Defs.

Axiom semax_set :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).

Axiom semax_fun_id:
  forall {CS: compspecs} {Espec: OracleKind},
      forall id f Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_specs Delta) ! id = Some f ->
    (glob_types Delta) ! id = Some (type_of_funspec f) ->
    @semax CS Espec Delta (P && `(func_ptr f) (eval_var id (type_of_funspec f)))
                  c Q ->
    @semax CS Espec Delta P c Q.

Axiom semax_unfold_Ssequence: forall {CS: compspecs} {Espec: OracleKind} c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, @semax CS Espec Delta P c1 Q -> @semax CS Espec Delta P c2 Q).

Axiom seq_assoc:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P s1 s2 s3 R,
        @semax CS Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        @semax CS Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.

Axiom semax_seq_skip:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s Q,
    @semax CS Espec Delta P s Q <-> @semax CS Espec Delta P (Ssequence s Sskip) Q.

Axiom semax_skip_seq:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s Q,
    @semax CS Espec Delta P s Q <-> @semax CS Espec Delta P (Ssequence Sskip s) Q.

Axiom semax_loop_nocontinue1:
  forall CS Espec Delta Pre s1 s2 s3 Post,
  nocontinue s1 = true ->
  nocontinue s2 = true ->
  nocontinue s3 = true ->
   @semax CS Espec Delta Pre (Sloop (Ssequence s1 (Ssequence s2 s3)) Sskip) Post ->
    @semax CS Espec Delta Pre (Sloop (Ssequence s1 s2) s3) Post.

Axiom semax_loop_nocontinue:
  forall {CS: compspecs} {Espec: OracleKind},
 forall Delta P body incr R,
 @semax CS Espec Delta P (Ssequence body incr) (loop_nocontinue_ret_assert P R) ->
 @semax CS Espec Delta P (Sloop body incr) R.

Axiom semax_convert_for_while':
 forall CS Espec Delta Pre s1 e2 s3 s4 s5 Post,
  nocontinue s4 = true ->
  nocontinue s3 = true -> 
  @semax CS Espec Delta Pre 
    (Ssequence s1 (Ssequence (Swhile e2 (Ssequence s4 s3)) s5)) Post ->
  @semax CS Espec Delta Pre (Ssequence (Sfor s1 e2 s4 s3) s5) Post.

Axiom semax_loop_unroll1:
  forall {CS: compspecs} {Espec: OracleKind} Delta P P' Q body incr R,
  @semax CS Espec Delta P body (loop1_ret_assert P' R) ->
  @semax CS Espec Delta P' incr (loop2_ret_assert Q R) ->
  @semax CS Espec Delta Q (Sloop body incr) R ->
  @semax CS Espec Delta P (Sloop body incr) R.

Axiom semax_if_seq:
 forall {CS: compspecs} {Espec: OracleKind} Delta P e c1 c2 c Q,
 semax Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.

Axiom semax_seq_Slabel:
   forall {cs:compspecs} {Espec: OracleKind},
     forall Delta (P:environ -> mpred) (c1 c2:statement) (Q:ret_assert) l,
   @semax cs Espec Delta P (Ssequence (Slabel l c1) c2) Q <-> 
   @semax cs Espec Delta P (Slabel l (Ssequence c1 c2)) Q.

(**************** END OF stuff from semax_rules ***********)

Axiom semax_frame:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s R F,
   closed_wrt_modvars s F ->
  @semax CS Espec Delta P s R ->
    @semax CS Espec Delta (P * F) s (frame_ret_assert R F).

Axiom semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (!!PP && P) c Q.

Axiom semax_extract_later_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta ((|> !!PP) && P) c Q.

Axiom semax_adapt_frame: forall {cs Espec} Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  derives (!!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && P rho))
                   (EX F: assert, (!!(closed_wrt_modvars c F) && (|={Ensembles.Full_set}=> P' rho * F rho) &&
                         !!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_normal (frame_ret_assert Q' F) rho |-- (|={Ensembles.Full_set}=> RA_normal Q rho)) &&
                         !!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_break (frame_ret_assert Q' F) rho |-- (|={Ensembles.Full_set}=> RA_break Q rho)) &&
                         !!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_continue (frame_ret_assert Q' F) rho |-- (|={Ensembles.Full_set}=> RA_continue Q rho)) &&
                         !!(forall vl rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_return (frame_ret_assert Q' F) vl rho |-- (RA_return Q vl rho)))))
   (SEM: @semax cs Espec Delta P' c Q'),
   @semax cs Espec Delta P c Q.

Axiom semax_adapt: forall {cs Espec} Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  !!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && P rho)
                   |-- ((|={Ensembles.Full_set}=> P' rho) &&
                        !!(forall rho, RA_normal Q' rho |-- (|={Ensembles.Full_set}=> RA_normal Q rho)) &&
                        !!(forall rho, RA_break Q' rho |-- (|={Ensembles.Full_set}=> RA_break Q rho)) &&
                        !!(forall rho, RA_continue Q' rho |-- (|={Ensembles.Full_set}=> RA_continue Q rho)) &&
                        !!(forall vl rho, RA_return Q' vl rho |-- (RA_return Q vl rho))))
   (SEM: @semax cs Espec Delta P' c Q'),
   @semax cs Espec Delta P c Q.

End PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.
