Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import sepcomp.Inlining.
Require Import sepcomp.Inliningspec.
Require Import RTL.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.reach.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.


Require Export Axioms.
Require Import RTL_eff.
Require Import RTL_coop.

Load Santiago_tactics.

Variable SrcProg: RTL.program.
Variable TrgProg: RTL.program.
Hypothesis TRANSF: transf_program SrcProg = OK TrgProg.
Let ge : RTL.genv := Genv.globalenv SrcProg.
Let tge : RTL.genv := Genv.globalenv TrgProg.
Let fenv := funenv_program SrcProg.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. apply Genv.find_symbol_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. apply Genv.find_var_info_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
    Genv.find_funct ge v = Some f ->
    exists f', Genv.find_funct tge v = Some f' /\ transf_fundef fenv f = OK f'.
Proof.
  eapply (Genv.find_funct_transf_partial (transf_fundef fenv) _ TRANSF).
Qed.
Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
    Genv.find_funct_ptr ge b = Some f ->
    exists f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef fenv f = OK f'.
Proof.
eapply (Genv.find_funct_ptr_transf_partial (transf_fundef fenv) _ TRANSF).
Qed.
Lemma sig_function_translated:
  forall f f', transf_fundef fenv f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto. 
  auto.
Qed.


(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. xomega. 
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
    context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. xomega.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq. 
  xomega.
Qed.

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> val_inject F rs#r rs'#(sreg ctx r))
  /\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ val_inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; xomega.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r). 
  left. rewrite B; auto. 
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
    agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> val_list_inject F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
    agree_regs F ctx rs rs' ->
    val_inject F v v' ->
    Ple r ctx.(mreg) ->
    agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto. 
  rewrite Regmap.gso. auto. xomega. 
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
    agree_regs F ctx rs rs' ->
    agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto. 
  rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
    agree_regs F ctx rs rs' ->
    agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
    agree_regs F ctx rs rs1 ->
    (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
    agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto. 
  apply shiftpos_above.
  eapply Plt_le_trans. apply shiftpos_below. xomega.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
    agree_regs F ctx rs1 rs2 ->
    inject_incr F F' ->
    agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto. 
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto. 
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
    val_list_inject F vl vl' ->
    (forall r, In r rl -> Ple r ctx.(mreg)) ->
    agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto. 
Qed.


(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
                                 forall rdsts rsrcs vl pc1 pc2 rs1,
                                   tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
                                   (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
                                   list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
                                   exists rs2,
                                     star step tge (State stk f sp pc1 rs1 m)
                                          E0 (State stk f sp pc2 rs2 m)
                                     /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
                                     /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
  (* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  (* rdsts = a :: rdsts *)
  inv H2. inv H0. 
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
    range_private F m m' sp lo hi ->
    (forall b delta ofs,
       F1 b = Some(sp, delta) ->
       Mem.perm m1 b ofs Max Nonempty ->
       lo <= ofs + delta < hi ->
       F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
    (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
    range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. omega. intros [P Q]. 
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
    range_private F m m' sp lo hi ->
    Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
    range_private F m m' sp' base hi ->
    Mem.alloc m 0 sz = (m1, sp) ->
    F1 sp = Some(sp', base) ->
    (forall b, b <> sp -> F1 b = F b) ->
    range_private F1 m1 m' sp' (base + Zmax sz 0) hi.
Proof.
  intros; red; intros. 
  exploit (H ofs). generalize (Zmax2 sz 0). omega. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4. 
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); omega.
  rewrite H2 in H4; auto. eelim B; eauto. 
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
    range_private F m m' sp (base + Zmax sz 0) hi ->
    Mem.free m b 0 sz = Some m1 ->
    F b = Some(sp, base) ->
    Mem.inject F m m' ->
    range_private F m1 m' sp base hi.
Proof.
  intros; red; intros. 
  destruct (zlt ofs (base + Zmax sz 0)) as [z|z].
  red; split. 
  replace ofs with ((ofs - base) + base) by omega.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); omega. 
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  exploit Mem.mi_no_overlap; eauto. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto. 
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  eapply Mem.perm_free_3; eauto. 
  intros [A | A]. congruence. omega. 

  exploit (H ofs). omega. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
    range_private F m1 m1' sp base hi ->
    (forall b ofs p,
       Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
    Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
    Mem.inject F m1 m1' ->
    inject_incr F F' ->
    inject_separated F F' m1 m1' ->
    Mem.valid_block m1' sp ->
    range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto. 
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. 
  red; intros; eelim B; eauto. eapply PERM; eauto. 
  red. destruct (plt b (Mem.nextblock m1)); auto. 
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto. 
Qed.


(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: block): Prop :=
| mk_match_globalenvs
    (DOMAIN: forall b, Plt b bound -> F b = Some(b, 0))
    (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
    (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
    (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
    (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
    find_function ge ros rs = Some fd ->
    agree_regs F ctx rs rs' ->
    match_globalenvs F bound ->
    exists fd',
      find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef fenv fd = OK fd'.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
  (* register *)
  assert (rs'#(sreg ctx r) = rs#r).
  exploit Genv.find_funct_inv; eauto. intros [b EQ].
  assert (A: val_inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
  rewrite EQ in A; inv A.
  inv H1. rewrite DOMAIN in H5. inv H5. auto.
  apply FUNCTIONS with fd. 
  rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  rewrite H2. eapply functions_translated; eauto.
  (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

(** ** Relating stacks *)

Inductive match_stacks (mu: SM_Injection) (m m': mem):
  list stackframe -> list stackframe -> block -> Prop :=
| match_stacks_nil: forall bound1 bound
                           (MG: match_globalenvs (as_inj mu) bound1)
                           (BELOW: Ple bound1 bound),
                      match_stacks mu m m' nil nil bound
| match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound ctx
                            (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                            (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
                            (AG: agree_regs (as_inj mu) ctx rs rs')
                            (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
(*locBlockSrc mu sp = true*)
(*locBlockTrg mu sp' = true*)
(PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
(SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
(SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
(RES: Ple res ctx.(mreg))
(BELOW: Plt sp' bound),
                       match_stacks (mu) m m'
                                    (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                    (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc) rs' :: stk')
                                    bound
| match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
                                  (MS: match_stacks_inside (mu) m m' stk stk' f' ctx sp' rs')
                                  (PRIV: range_private (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
                                  (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                                  (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
                                  (RET: ctx.(retinfo) = Some (rpc, res))
(*locBlockTrg mu sp' = true*)
(BELOW: Plt sp' bound),
                             match_stacks (mu) m m'
                                          stk
                                          (Stackframe res f' (Vptr sp' Int.zero) rpc rs' :: stk')
                                          bound

with match_stacks_inside (mu: SM_Injection) (m m': mem):
       list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
     | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
                                        (MS: match_stacks (mu) m m' stk stk' sp')
(*locBlockTrg mu sp' = true*)(*Maybe*)
(RET: ctx.(retinfo) = None)
(DSTK: ctx.(dstk) = 0),
                                   match_stacks_inside (mu) m m' stk stk' f' ctx sp' rs'
     | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' ctx sp' rs' ctx'
                                           (MS: match_stacks_inside (mu) m m' stk stk' f' ctx' sp' rs')
                                           (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
                                           (AG: agree_regs (as_inj mu) ctx' rs rs')
                                           (SP: (as_inj mu) sp = Some(sp', ctx'.(dstk)))
(*locBlockSrc mu sp = true*)
(*locBlockTrg mu sp' = true*)
(PAD: range_private (as_inj mu) m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
(RES: Ple res ctx'.(mreg))
(RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
(BELOW: context_below ctx' ctx)
(SBELOW: context_stack_call ctx' ctx),
                                      match_stacks_inside (mu) m m' (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                                          stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.


  Variable F: SM_Injection.
  Let Finj := as_inj F.
  Variables m m': mem.

  Lemma match_stacks_globalenvs:
    forall stk stk' bound,
      match_stacks F m m' stk stk' bound -> exists b, match_globalenvs Finj b
                                                      with match_stacks_inside_globalenvs:
                                                             forall stk stk' f ctx sp rs', 
                                                               match_stacks_inside F m m' stk stk' f ctx sp rs' -> exists b, match_globalenvs Finj b.
  Proof.
    induction 1; eauto.
    induction 1; eauto.
  Qed.

  Lemma match_globalenvs_preserves_globals:
    forall b, match_globalenvs Finj b -> meminj_preserves_globals ge Finj.
  Proof.
    intros. inv H. red. split. eauto. split. eauto.
    intros. symmetry. eapply IMAGE; eauto.
  Qed. 

  Lemma match_stacks_inside_globals:
    forall stk stk' f ctx sp rs', 
      match_stacks_inside F m m' stk stk' f ctx sp rs' -> meminj_preserves_globals ge Finj.
  Proof.
    intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A]. 
    eapply match_globalenvs_preserves_globals; eauto.
  Qed.

  Lemma match_stacks_bound:
    forall stk stk' bound bound1,
      match_stacks F m m' stk stk' bound ->
      Ple bound bound1 ->
      match_stacks F m m' stk stk' bound1.
  Proof.
    intros. inv H.
    apply match_stacks_nil with bound0. auto. eapply Ple_trans; eauto. 
    eapply match_stacks_cons; eauto. eapply Plt_le_trans; eauto. 
    eapply match_stacks_untailcall; eauto. eapply Plt_le_trans; eauto. 
  Qed. 

  Variable F1: SM_Injection.
  Let Finj1 := as_inj F1.
  Variables m1 m1': mem.
  Hypothesis INCR: inject_incr Finj Finj1.

  Lemma match_stacks_invariant:
    forall stk stk' bound, match_stacks F m m' stk stk' bound ->
                           forall (INJ: forall b1 b2 delta, 
                                          Finj1 b1 = Some(b2, delta) -> Plt b2 bound -> Finj b1 = Some(b2, delta))
                                  (PERM1: forall b1 b2 delta ofs,
                                            Finj1 b1 = Some(b2, delta) -> Plt b2 bound ->
                                            Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
                                  (PERM2: forall b ofs, Plt b bound ->
                                                        Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
                                  (PERM3: forall b ofs k p, Plt b bound ->
                                                            Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
                             match_stacks F1 m1 m1' stk stk' bound

                             with match_stacks_inside_invariant:
                                    forall stk stk' f' ctx sp' rs1, 
                                      match_stacks_inside F m m' stk stk' f' ctx sp' rs1 ->
                                      forall rs2
                                             (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
                                             (INJ: forall b1 b2 delta, 
                                                     Finj1 b1 = Some(b2, delta) -> Ple b2 sp' -> Finj b1 = Some(b2, delta))
                                             (PERM1: forall b1 b2 delta ofs,
                                                       Finj1 b1 = Some(b2, delta) -> Ple b2 sp' ->
                                                       Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
                                             (PERM2: forall b ofs, Ple b sp' ->
                                                                   Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
                                             (PERM3: forall b ofs k p, Ple b sp' ->
                                                                       Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
                                        match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs2.

  Proof.
    induction 1; intros.
    (* nil *)
    apply match_stacks_nil with (bound1 := bound1).
    inv MG. constructor; auto. 
    intros. apply IMAGE with delta. eapply INJ; eauto. eapply Plt_le_trans; eauto.
    auto. auto.
    (* cons *)
    apply match_stacks_cons with (ctx := ctx); auto.
    eapply match_stacks_inside_invariant; eauto.
    intros; eapply INJ; eauto; xomega. 
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    eapply agree_regs_incr; eauto.
    eapply range_private_invariant; eauto. 
    (* untailcall *)
    apply match_stacks_untailcall with (ctx := ctx); auto. 
    eapply match_stacks_inside_invariant; eauto.
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    eapply range_private_invariant; eauto. 

    induction 1; intros.
    (* base *)
    eapply match_stacks_inside_base; eauto.
    eapply match_stacks_invariant; eauto. 
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    (* inlined *)
    apply match_stacks_inside_inlined with (ctx' := ctx'); auto. 
    apply IHmatch_stacks_inside; auto.
    intros. apply RS. red in BELOW. xomega. 
    apply agree_regs_incr with Finj; auto. 
    apply agree_regs_invariant with rs'; auto. 
    intros. apply RS. red in BELOW. xomega. 
    eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. xomega. eapply PERM1; eauto. xomega.
    intros. eapply PERM2; eauto. xomega.
  Qed.

  Lemma match_stacks_empty:
    forall stk stk' bound,
      match_stacks F m m' stk stk' bound -> stk = nil -> stk' = nil
      with match_stacks_inside_empty:
             forall stk stk' f ctx sp rs,
               match_stacks_inside F m m' stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
  Proof.
    induction 1; intros.
    auto.
    discriminate.
    exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
    induction 1; intros.
    split. eapply match_stacks_empty; eauto. auto.
    discriminate.
  Qed.

End MATCH_STACKS.



(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v, 
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    match_stacks_inside F m m' stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto. 
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. xomega.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1', 
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    Mem.store chunk m b ofs v = Some m1 ->
    Mem.store chunk' m' b' ofs' v' = Some m1' ->
    match_stacks_inside F m1 m1' stk stk' f' ctx sp' rs'.
Proof.
  intros. 
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sp' rs',
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    forall sz m1 b F1 delta,
      Mem.alloc m 0 sz = (m1, b) ->
      inject_incr (as_inj F) (as_inj F1) ->
      (as_inj F1) b = Some(sp', delta) ->
      (forall b1, b1 <> b -> (as_inj F1) b1 = (as_inj F) b1) ->
      delta >= ctx.(dstk) ->
      match_stacks_inside F1 m1 m' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto. 
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H4; inv H4. eelim Plt_strict; eauto. 
  rewrite H2 in H4; auto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H1 in H4. inv H4. eelim Plt_strict; eauto. 
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto. 
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. omega. 
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H2 in H5; inv H5. elimtype False; xomega. 
  rewrite H3 in H5; auto. 
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1,
    match_stacks F m m' stk stk' sp ->
    Mem.free m b lo hi = Some m1 ->
    match_stacks F m1 m' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto. 
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sp lo hi m1',
    match_stacks F m m' stk stk' sp ->
    Mem.free m' sp lo hi = Some m1' ->
    match_stacks F m m1' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto. 
  intros. eapply Mem.perm_free_1; eauto. 
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H. 
  assert (2 <= sz -> (2 | n)). intros.
  destruct (zle sz 1). omegaContradiction.
  destruct (zle sz 2). auto. 
  destruct (zle sz 4). apply Zdivides_trans with 4; auto. exists 2; auto.
  apply Zdivides_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
  destruct (zle sz 1). omegaContradiction.
  destruct (zle sz 2). omegaContradiction.
  destruct (zle sz 4). auto.
  apply Zdivides_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
  destruct (zle sz 1). omegaContradiction.
  destruct (zle sz 2). omegaContradiction.
  destruct (zle sz 4). omegaContradiction.
  auto.
  destruct chunk; simpl in *; auto.
  apply Zone_divide.
  apply Zone_divide.
  apply H2; omega.
Qed.


(** Preservation by external calls *)

Section EXTCALL.

  Variables F1 F2: SM_Injection.
  Let Finj1 := as_inj F1.
  Let Finj2 := as_inj F2.
  Variables m1 m2 m1' m2': mem.
  Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
  Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
  Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach Finj1 m1) m1' m2'.
  Hypothesis INJ: Mem.inject Finj1 m1 m1'.
  Hypothesis INCR: inject_incr Finj1 Finj2.
  Hypothesis SEP: inject_separated Finj1 Finj2 m1 m1'.

  Lemma match_stacks_extcall:
    forall stk stk' bound, 
      match_stacks F1 m1 m1' stk stk' bound ->
      Ple bound (Mem.nextblock m1') ->
      match_stacks F2 m2 m2' stk stk' bound
      with match_stacks_inside_extcall:
             forall stk stk' f' ctx sp' rs',
               match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs' ->
               Plt sp' (Mem.nextblock m1') ->
               match_stacks_inside F2 m2 m2' stk stk' f' ctx sp' rs'.
  Proof.
    induction 1; intros.
    apply match_stacks_nil with bound1; auto. 
    inv MG. constructor; intros; eauto. 
    destruct (Finj1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; unfold Finj2 in EQ; rewrite H0 in EQ; inv EQ.
    eapply IMAGE; eauto. 
    exploit SEP; eauto. intros [A B]. elim B. red. xomega. 
    eapply match_stacks_cons; eauto. 
    eapply match_stacks_inside_extcall; eauto. xomega. 
    eapply agree_regs_incr; eauto. 
    eapply range_private_extcall; eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
    eapply match_stacks_untailcall; eauto. 
    eapply match_stacks_inside_extcall; eauto. xomega. 
    eapply range_private_extcall; eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
    induction 1; intros.
    eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. xomega. 
    eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_incr; eauto. 
    eapply range_private_extcall; eauto.
  Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq. 
  apply Zdiv_unique with (b := amount - 1). omega. omega.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall F m m' stk stk' f' ctx sp' rs' ctx' f,
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    context_below ctx ctx' ->
    context_stack_tailcall ctx f ctx' ->
    ctx'.(retinfo) = ctx.(retinfo) ->
    range_private (as_inj F) m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
    tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
    match_stacks_inside F m m' stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence. 
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Zdivide_0.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto. 
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply H3. inv H4. xomega. 
  congruence. 
  unfold context_below in *. xomega.
  unfold context_stack_call in *. omega. 
Qed.

(** ** Relating states *)

Inductive match_states:  SM_Injection -> RTL_core -> mem -> RTL_core -> mem -> Prop :=
| match_regular_states: forall mu stk f sp pc rs m stk' f' sp' rs' m' ctx
                               (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                               (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
                               (AG: agree_regs (as_inj mu) ctx rs rs')
                               (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
                               (MINJ: Mem.inject (as_inj mu) m m')
                               (VB: Mem.valid_block m' sp')
                               (PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
                               (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                               (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
                          match_states mu (RTL_State stk f (Vptr sp Int.zero) pc rs) m
                                       (RTL_State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs') m'
| match_call_states: forall (mu: SM_Injection) stk fd args m stk' fd' args' m'
                            (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
                            (FD: transf_fundef fenv fd = OK fd')
                            (VINJ: val_list_inject  (as_inj mu) args args')
                            (MINJ: Mem.inject (as_inj mu) m m'),
                       match_states mu (RTL_Callstate stk fd args) m
                                    (RTL_Callstate stk' fd' args') m'
| match_call_regular_states: forall (mu: SM_Injection) stk f vargs m stk' f' sp' rs' m' ctx ctx' pc' pc1' rargs
                                    (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                                    (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
                                    (BELOW: context_below ctx' ctx)
                                    (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
                                    (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
                                    (VINJ: list_forall2 (val_reg_charact (as_inj mu) ctx' rs') vargs rargs)
                                    (MINJ: Mem.inject (as_inj mu) m m')
                                    (VB: Mem.valid_block m' sp')
                                    (PRIV: range_private  (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
                                    (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                                    (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
                               match_states mu (RTL_Callstate stk (Internal f) vargs) m
                                            (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'
| match_return_states: forall (mu: SM_Injection) stk v m stk' v' m'
                              (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
                              (VINJ: val_inject (as_inj mu) v v')
                              (MINJ: Mem.inject (as_inj mu) m m'),
                         match_states mu (RTL_Returnstate stk v) m
                                      (RTL_Returnstate stk' v') m'
| match_return_regular_states: forall (mu: SM_Injection)stk v m stk' f' sp' rs' m' ctx pc' or rinfo
                                      (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                                      (RET: ctx.(retinfo) = Some rinfo)
                                      (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
                                      (VINJ: match or with None => v = Vundef | Some r => val_inject (as_inj mu) v rs'#(sreg ctx r) end)
                                      (MINJ: Mem.inject (as_inj mu) m m')
                                      (VB: Mem.valid_block m' sp')
                                      (PRIV: range_private (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
                                      (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                                      (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
                                 match_states mu (RTL_Returnstate stk v) m
                                              (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'.

Print REACH_closed.
About REACH.
Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\
  SM_wd mu /\
  Mem.inject (as_inj mu) m1 m2.

(** ** Forward simulation *)
Definition RTL_measure (S: RTL_core) : nat :=
  match S with
  | RTL_State _ _ _ _ _ => 1%nat
  | RTL_Callstate _ _ _ => 0%nat
  | RTL_Returnstate _ _ => 0%nat
  end.


Lemma tr_funbody_inv:
  forall sz cts f c pc i,
    tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto. 
Qed.

(** MISSING THEOREM step_simulation *)


Definition entry_points_ok entrypoints:= forall (v1 v2 : val) (sig : signature),
                                             In (v1, v2, sig) entrypoints -> 
                                             exists b f1 f2, 
                                               v1 = Vptr b Int.zero 
                                               /\ v2 = Vptr b Int.zero
                                               /\ Genv.find_funct_ptr ge b = Some f1
                                               /\ Genv.find_funct_ptr tge b = Some f2.

(** ** Behold the theorem *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs SrcProg)))
         (entrypoints : list (val * val * signature))
         (entry_ok : entry_points_ok entrypoints)
         (init_mem: exists m0, Genv.init_mem SrcProg = Some m0),
    SM_simulation.SM_simulation_inject rtl_eff_sem
                                       rtl_eff_sem ge tge entrypoints.


  intros.
  (*eapply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf.*)
  eapply sepcomp.effect_simulations_lemmas.inj_simulation_star with (match_states:= MATCH)(measure:= RTL_measure).

  Lemma environment_equality: (exists m0:mem, Genv.init_mem SrcProg = Some m0) -> 
                                     genvs_domain_eq ge tge.
    descend;
    destruct H0 as [b0]; exists b0;
    rewriter_back;
    [rewrite symbols_preserved| rewrite <- symbols_preserved| rewrite varinfo_preserved| rewrite <- varinfo_preserved]; reflexivity.
  Qed.
  Hint Resolve environment_equality: trans_correct.
  auto with trans_correct.

  Lemma MATCH_wd: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                         (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:MATCH d mu c1 m1 c2 m2), SM_wd mu.
    intros. eapply MC. Qed.
  Hint Resolve MATCH_wd: trans_correct.
  eauto with trans_correct.

  Lemma MATCH_RC: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                         (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:
                                                                  MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
    intros. eapply MC. Qed.
  Hint Resolve MATCH_RC: trans_correct.
  eauto with trans_correct.


Lemma MATCH_restrict: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                 (m1 : mem) (c2 : RTL_core) (m2 : mem) (X : block -> bool) (MC: MATCH d mu c1 m1 c2 m2)(HX: forall b : block, vis mu b = true -> X b = true)(RC0:REACH_closed m1 X), MATCH d (restrict_sm mu X) c1 m1 c2 m2.
intros.
Proof. intros.
  destruct MC as [MC [RC [PG [GF [VAL [WDmu [INJ GFP]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.

split.

Lemma match_states_restrict: forall mu m1 m2 c1 c2 X
      (HX: forall b, vis mu b = true -> X b = true)
      (RC: REACH_closed m1 X)
      (MCS: match_states mu c1 m1 c2 m2 ),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
  admit.
Qed.

apply match_states_restrict; intuition.

split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. (*clear -PG HX.*)
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply GF.
split.
destruct VAL.
(*This should be a lemma*)
unfold sm_valid.
    rewrite restrict_sm_DOM.
    rewrite restrict_sm_RNG.
    split; intros; intuition.
split. assumption.
(*split.*)
 rewrite restrict_sm_all.
eapply  inject_restrict; repeat (first [assumption| split]).
Qed.
Hint Resolve MATCH_restrict: trans_correct.
auto with trans_correct.

Lemma MATCH_valid:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                              (m1 : mem) (c2 : RTL_core) (m2 : mem)
                         (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
intros.
apply MC.
Qed.

Hint Resolve MATCH_valid: trans_correct.
eauto with trans_correct.

Lemma MATCH_PG:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                           (m1 : mem) (c2 : RTL_core) (m2 : mem)(
                                      MC: MATCH d mu c1 m1 c2 m2),
                                      meminj_preserves_globals ge (extern_of mu) /\
                                      (forall b : block,
                                         isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.
Hint Resolve MATCH_PG: trans_correct.
eauto with trans_correct.

Lemma MATCH_initial_core: forall (v1 v2 : val) (sig : signature) entrypoints
  (entry_ok : entry_points_ok entrypoints)
   (EP: In (v1, v2, sig) entrypoints)
   (vals1 : list val) (c1 : RTL_core) (m1 : mem) 
     (j : meminj) (vals2 : list val) (m2 : mem) (DomS DomT : block -> bool)
   (SM_Ini:initial_core rtl_eff_sem ge v1 vals1 = Some c1)
   (Inj: Mem.inject j m1 m2)
   (VInj: Forall2 (val_inject j) vals1 vals2)
   (PG: meminj_preserves_globals ge j)
   (J: forall (b1 b2 : block) (d : Z),
    j b1 = Some (b2, d) -> DomS b1 = true /\ DomT b2 = true)
   (RCH: forall b : block,
    REACH m2 (fun b' : block => isGlobalBlock tge b' || getBlocks vals2 b')
      b = true -> DomT b = true)
   (HDomS: (forall b : block, DomS b = true -> Mem.valid_block m1 b))
   (HDomT: (forall b : block, DomT b = true -> Mem.valid_block m2 b)),
   exists c2 : RTL_core,
     initial_core rtl_eff_sem tge v2 vals2 = Some c2 /\
     MATCH c1
       (initial_SM DomS DomT DomS DomT j) (*
          (REACH m1
             (fun b : block => isGlobalBlock ge b || getBlocks vals1 b))
          (REACH m2
             (fun b : block => isGlobalBlock tge b || getBlocks vals2 b)) j)*)
       c1 m1 c2 m2.
 Proof.
  intros.
  inversion SM_Ini.
  unfold  RTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exists (RTL_Callstate nil tf vals2).
  split. 
  simpl. 
  destruct (entry_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  subst. inv A.
  unfold ge, tge in *. rewrite C in Heqzz. inv Heqzz. 
  rewrite D in FIND. inv FIND.
  unfold RTL_initial_core. 
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
  solve[rewrite D; auto].
  intros CONTRA.
  solve[elimtype False; auto].
  admit.
Qed.
Hint Resolve MATCH_initial_core: trans_correct.
eauto with trans_correct.

Lemma Match_Halted: forall (cd : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
     (m1 : mem) (c2 : RTL_core) (m2 : mem) (v1 : val)(MC:
   MATCH cd mu c1 m1 c2 m2)(HALT:
   halted rtl_eff_sem c1 = Some v1),
   exists v2 : val,
     Mem.inject (as_inj mu) m1 m2 /\
     val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
     halted rtl_eff_sem c2 = Some v2.
Proof.
intros.
unfold MATCH in MC; destruct MC as [H0 H1].
inv H0; simpl in *; inv HALT. 
Print match_states.
inv MS. 
exists v'; split; try assumption; split; try reflexivity; inv H0. admit.
inv H0.
inv MS0; [rewrite RET in RET0; inv RET0 | inv H0].
inv MS.
rewrite RET in RET0; inv RET0.
inv H0.
Qed.
Hint Resolve Match_Halted: trans_correct.
eauto with trans_correct.

Lemma at_external_lemma: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) 
                                (c2 : RTL_core) (m2 : mem) (e : external_function) 
                                (vals1 : list val) (ef_sig : signature)(MC: MATCH c1 mu c1 m1 c2 m2) (ATE: at_external rtl_eff_sem c1 = Some (e, ef_sig, vals1)),
                           Mem.inject (as_inj mu) m1 m2 /\ 
                           (exists vals2 : list val, Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\ at_external rtl_eff_sem c2 = Some (e, ef_sig, vals2)).
  intros.
  split. inv MC; apply H0.
  inv MC; simpl in *. inv H; inv ATE.
  destruct fd; inv H1.
  exists args'.
  split. apply val_list_inject_forall_inject. admit.
  inv FD; trivial.
Qed.
Hint Resolve at_external_lemma: trans_correct.
eauto with trans_correct.

Lemma Match_AfterExternal: 
forall (mu : SM_Injection) (st1 : RTL_core) (st2 : RTL_core) (m1 : mem) (e : external_function) (vals1 : list val) (m2 : mem) (ef_sig : signature) (vals2 : list val) (e' : external_function) (ef_sig' : signature) 
       (MemInjMu : Mem.inject (as_inj mu) m1 m2)
       (MatchMu : MATCH st1 mu st1 m1 st2 m2)
       (AtExtSrc : at_external rtl_eff_sem st1 = Some (e, ef_sig, vals1))
       (AtExtTgt : at_external rtl_eff_sem st2 = Some (e', ef_sig', vals2))
       (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
       (pubSrc' : block -> bool)
       (pubSrcHyp : pubSrc' =
              (fun b : block =>
               locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgt' : block -> bool)
       (pubTgtHyp : pubTgt' =
              (fun b : block =>
               locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       (nu : SM_Injection)
       (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
       (nu' : SM_Injection)
       (ret1 : val)
       (m1' : mem)
       (ret2 : val)
       (m2' : mem)
       (INC : extern_incr nu nu')
       (SEP : sm_inject_separated nu nu' m1 m2)
       (WDnu' : SM_wd nu')
       (SMvalNu' : sm_valid nu' m1' m2')
       (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
       (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
       (FwdSrc : mem_forward m1 m1')
       (FwdTgt : mem_forward m2 m2')
       (frgnSrc' : block -> bool)
       (frgnSrcHyp : frgnSrc' =
               (fun b : block =>
                DomSrc nu' b &&
                (negb (locBlocksSrc nu' b) &&
                 REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
       (frgnTgt' : block -> bool)
       (frgnTgtHyp : frgnTgt' =
               (fun b : block =>
                DomTgt nu' b &&
                (negb (locBlocksTgt nu' b) &&
                 REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
       (mu' : SM_Injection)
       (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
       (UnchPrivSrc : Mem.unchanged_on
                  (fun (b : block) (_ : Z) =>
                   locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
       (UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists (st1' st2' : RTL_core),
  after_external rtl_eff_sem (Some ret1) st1 = Some st1' /\
  after_external rtl_eff_sem (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros. 
 destruct MatchMu as [MC [RC [PG [GF [VAL [WDmu [INJ GFP]]]]]]].
 inv MC; simpl in *; inv AtExtSrc.
  destruct fd; inv H0.
  destruct fd'; inv AtExtTgt.
  exists (RTL_Returnstate stk ret1). eexists.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
inv FD.
assert (INCvisNu': inject_incr
  (restrict (as_inj nu')
     (vis
        (replace_externs nu'
           (fun b : Values.block =>
            DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
           (fun b : Values.block =>
            DomTgt nu' b &&
            (negb (locBlocksTgt nu' b) &&
             REACH m2' (exportedTgt nu' (ret2 :: nil)) b))))) (as_inj nu')).
      unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
      apply restrict_incr. 
assert (RC': REACH_closed m1' (mapped (as_inj nu'))).
        eapply inject_REACH_closed; eassumption.
assert (PHnu': meminj_preserves_globals (Genv.globalenv SrcProg) (as_inj nu')).
    subst. clear - INC SEP PG GF WDmu WDnu'.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    apply meminj_preserves_genv2blocks.
    split; intros.
      specialize (PGa _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      apply foreign_in_extern.
     assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char1 in H.
          rewrite H. trivial.
      Check frgnSrc.
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      assumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern. 
      assert (GG: isGlobalBlock ge b = true). (*4 goals*)
          unfold isGlobalBlock, ge. apply genv2blocksBool_char2 in H.
          rewrite H. intuition. (*3 goals*)
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
      apply foreign_in_extern; eassumption. (*2 goals*)
    eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
      remember (as_inj mu b1) as d.
      destruct d; apply eq_sym in Heqd. (*3 goals*)
        destruct p. 
        apply extern_incr_as_inj in INC; trivial. (*3 goals*)
        rewrite replace_locals_as_inj in INC.
        rewrite (INC _ _ _ Heqd) in H0. trivial. (*3 goals*)
      destruct SEP as [SEPa _].
        rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in SEPa. 
        destruct (SEPa _ _ _ Heqd H0).
        destruct (as_inj_DomRng _ _ _ _ PGb WDmu).
        congruence. (*1 goal*)
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H1); clear H1.
  apply orb_true_iff in IHL.
  remember (locBlocksSrc nu' b') as l.
  destruct l; apply eq_sym in Heql.
  (*case locBlocksSrc nu' b' = true*)
    clear IHL.
    remember (pubBlocksSrc nu' b') as p.
    destruct p; apply eq_sym in Heqp.
      assert (Rb': REACH m1' (mapped (as_inj nu')) b' = true).
        apply REACH_nil. 
        destruct (pubSrc _ WDnu' _ Heqp) as [bb2 [dd1 [PUB PT]]].
        eapply mappedI_true.
         apply (pub_in_all _ WDnu' _ _ _ PUB).
      assert (Rb:  REACH m1' (mapped (as_inj nu')) b = true).
        eapply REACH_cons; try eassumption.
      specialize (RC' _ Rb).
      destruct (mappedD_true _ _ RC') as [[b2 d1] AI'].
      remember (locBlocksSrc nu' b) as d.
      destruct d; simpl; trivial.
      apply andb_true_iff. 
      split. eapply as_inj_DomRng; try eassumption.
      eapply REACH_cons; try eassumption.
        apply REACH_nil. unfold exportedSrc.
        rewrite (pubSrc_shared _ WDnu' _ Heqp). intuition.
      destruct (UnchPrivSrc) as [UP UV]; clear UnchLOOR.
        specialize (UP b' z Cur Readable). 
        specialize (UV b' z). 
        destruct INC as [_ [_ [_ [_ [LCnu' [_ [PBnu' [_ [FRGnu' _]]]]]]]]].
        rewrite <- LCnu'. rewrite replace_locals_locBlocksSrc.  
        rewrite <- LCnu' in Heql. rewrite replace_locals_locBlocksSrc in *.
        rewrite <- PBnu' in Heqp. rewrite replace_locals_pubBlocksSrc in *.
        clear INCvisNu'. 
        rewrite Heql in *. simpl in *. intuition.
        assert (VB: Mem.valid_block m1 b').
          eapply VAL. unfold DOM, DomSrc. rewrite Heql. intuition.
        apply (H VB) in H2.
        rewrite (H0 H2) in H4. clear H H0.
        remember (locBlocksSrc mu b) as q.
        destruct q; simpl; trivial; apply eq_sym in Heqq.
        assert (Rb : REACH m1 (vis mu) b = true).
           eapply REACH_cons; try eassumption.
           apply REACH_nil. unfold vis. rewrite Heql; trivial.
        specialize (RC _ Rb). unfold vis in RC.
           rewrite Heqq in RC; simpl in *.
        rewrite replace_locals_frgnBlocksSrc in FRGnu'.
        rewrite FRGnu' in RC.
        apply andb_true_iff.  
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ RC). intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ RC). intuition.
  (*case DomSrc nu' b' &&
    (negb (locBlocksSrc nu' b') &&
     REACH m1' (exportedSrc nu' (ret1 :: nil)) b') = true*)
    destruct IHL. inv H.
    apply andb_true_iff in H. simpl in H. 
    destruct H as[DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchLOOR UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ MemInjNu' RET
               _ Rb' (fun b => true)) as [b2 [d1 [AI' _]]]; trivial.
           assert (REACH m1' (mapped (as_inj nu')) b = true).
             eapply REACH_cons; try eassumption.
             apply REACH_nil. eapply mappedI_true; eassumption.
           specialize (RC' _ H). 
           destruct (mappedD_true _ _ RC') as [[? ?] ?].
           eapply as_inj_DomRng; eassumption.
    eapply REACH_cons; try eassumption.
(*assert (RRR: REACH_closed m1' (exportedSrc nu' (ret1 :: nil))).
    intros b Hb. apply REACHAX in Hb.
       destruct Hb as [L HL].
       generalize dependent b.
       induction L ; simpl; intros; inv HL; trivial.
       specialize (IHL _ H1); clear H1.
       unfold exportedSrc.
       eapply REACH_cons; eassumption.*)

assert (RRC: REACH_closed m1' (fun b : Values.block =>
                         mapped (as_inj nu') b &&
                           (locBlocksSrc nu' b
                            || DomSrc nu' b &&
                               (negb (locBlocksSrc nu' b) &&
                           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
  eapply REACH_closed_intersection; eassumption.
assert (GFnu': forall b, isGlobalBlock (Genv.globalenv SrcProg) b = true ->
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
     intros. specialize (GF _ H).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in GF.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ GF). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ GF). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ GF). intuition.
split.
  unfold vis in *.
  rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
  econstructor; try eassumption.
  admit.
  rewrite replace_externs_as_inj. assumption.
admit.
unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
Qed.

Hint Resolve Match_AfterExternal: trans_correct.
eauto with trans_correct.

clear entry_ok.
clear init_mem.


Ltac extend_smart:=  let x := fresh "x" in extensionality x.
  Ltac rewrite_freshloc := match goal with
                             | H: (Mem.storev _ _ _ _ = Some _) |- _ => rewrite (storev_freshloc _ _ _ _ _ H)
                             | H: (Mem.free _ _ _ _ = Some _) |- _ => apply freshloc_free in H; rewrite H
                             | _ => try rewrite freshloc_irrefl
                           end.
  Ltac loc_alloc_solve := apply sm_locally_allocatedChar; repeat split; try extend_smart;
                          try rewrite_freshloc; intuition.
Print sm_locally_allocated.

  Lemma step_simulation_noeffect: forall (st1 : RTL_core) (m1 : mem) (st1' : RTL_core) (m1' : mem)
                                         (CS: corestep rtl_eff_sem ge st1 m1 st1' m1')
                                         (st2 : RTL_core) (mu : SM_Injection) (m2 : mem)
                                         (MC:MATCH st1 mu st1 m1 st2 m2),
                                  exists (st2' : RTL_core) (m2' : mem),
                                    (corestep_plus rtl_eff_sem tge st2 m2 st2' m2' \/
                                     (RTL_measure st1' < RTL_measure st1)%nat /\
                                     corestep_star rtl_eff_sem tge st2 m2 st2' m2') /\
                                    exists (mu' : SM_Injection),
                                      intern_incr mu mu' /\
                                      sm_inject_separated mu mu' m1 m2 /\
                                      sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                                      MATCH st1' mu' st1' m1' st2' m2'.
    
    intros.
    simpl in *.
    destruct MC as [MS H].
    
    inv CS;
      inv MS.
    (* Inop *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    eexists. eexists. 

    split.
    left.
    eapply corestep_plus_one.
    eapply rtl_corestep_exec_Inop. eassumption.
    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH.
    intuition.
    eapply match_regular_states; first [eassumption| split; eassumption].


    (* Iop *)
    Focus 1.
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    repeat open_Hyp.
    exploit eval_operation_inject. 

    eapply match_stacks_inside_globals; eauto.
    exact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
    fold (sop ctx op). intros [v' [A B]].
    eexists. eexists.
    split; simpl.
    left. 
    eapply corestep_plus_one. 

    eapply rtl_corestep_exec_Iop. eassumption.
    erewrite eval_operation_preserved; eauto.
    exact symbols_preserved. 
    econstructor; eauto. 
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH.
    intuition.
    eapply match_regular_states; eauto.


    apply match_stacks_inside_set_reg; auto.
    apply agree_set_reg; auto. 


    (* Iload *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
    fold (saddr ctx addr). intros [a' [P Q]].
    exploit Mem.loadv_inject; eauto. intros [v' [U V]].
    assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
    eexists. eexists.
    split; simpl. left.
    eapply corestep_plus_one. 
    eapply rtl_corestep_exec_Iload; try eassumption.
    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH;
      intuition.
    eapply match_regular_states; eauto.
    apply match_stacks_inside_set_reg; auto.
    apply agree_set_reg; auto.
    

    (* Istore *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    exploit eval_addressing_inject.
    About eval_addressing_inject.
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
    fold saddr. intros [a' [P Q]].
    exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto. 
    intros [m2' [U V]].
    assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
    eexists. eexists.
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_Istore; eauto.

    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.


    Focus.
    destruct a; simpl in H1; try discriminate.
    destruct a'; simpl in U; try discriminate.
    unfold MATCH;
    intuition.
    econstructor; eauto.
    eapply match_stacks_inside_store; eauto.
    eapply Mem.store_valid_block_1; eauto.
    eapply range_private_invariant; eauto.
    intros; split; auto. eapply Mem.perm_store_2; eauto.
    intros; eapply Mem.perm_store_1; eauto.
    intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.
    inv H2.
    eapply REACH_Store; 
    try eassumption.
    assert (VINJ1: val_inject (restrict (as_inj mu) (vis mu)) (Vptr b i) (Vptr b0 i0)).
    admit.
    inv VINJ1.
    apply (restrictD_Some _ _ _ _ _ H15).
     intros b' Hb'. rewrite getBlocksD, getBlocksD_nil in Hb'.
     destruct (rs # src); inv Hb'. 
     rewrite orb_false_r in H10.
       rewrite H10. simpl.
       assert (b1=b').
       remember (eq_block b1 b') as d.
          destruct d; intuition.
       subst. 
    assert (VINJ2: val_inject (restrict (as_inj mu) (vis mu)) (Vptr b' i) (Vptr b0 i0)).
    admit.
       inv VINJ2. apply (restrictD_Some _ _ _ _ _ H16).
      (* sm_valid mu m1' m2' *)
    split; intros. 
      eapply storev_valid_block_1; try eassumption.
      eapply H8; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
      eapply H8; assumption.
    


(**)
    (* Icall *)
    Focus 1.
    exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
    exploit find_function_agree; eauto. intros [fd' [A B]].
    exploit tr_funbody_inv; eauto. intros TR. inv TR.

    (* not inlined *)
    eexists. eexists.
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_Icall; eauto.
    Print rtl_corestep_exec_Icall.
    eapply sig_function_translated; eauto.
    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    split.
    econstructor; eauto.
    eapply match_stacks_cons; eauto.
    eapply agree_val_regs; eauto.   
    intuition.

    (* inlined *)
    assert (fd = Internal f0).
    simpl in H1. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat SrcProg). 
    try eassumption. eauto. intros. 
    unfold ge in H1. congruence.
    subst fd.
    
    eexists. eexists.
    split; simpl.
    right; split. simpl; omega.
    eapply corestep_star_zero.

    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
    intuition.
    Focus 1.
    eapply match_call_regular_states; eauto. (* match_call_regular_states*)
    eapply match_stacks_inside_inlined; eauto.
    red; intros. apply PRIV. inv H14. destruct H17.
    xomega.
    apply agree_val_regs_gen; auto.
    red; intros; apply PRIV. destruct H17. omega.

    (* Itailcall *)
    exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
    exploit find_function_agree; eauto. intros [fd' [A B]].
    assert (PRIV': range_private (as_inj mu) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    eapply range_private_free_left; eauto. inv FB. rewrite <- H5. auto. 
    exploit tr_funbody_inv; eauto. 
    intros TR. 
    inv TR.

    (* within the original function *)
    inv MS0; try congruence.

    assert (X: { m1' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto. xomega.
    destruct X as [m2' FREE].
    
    eexists. eexists.
    split; simpl.
    left. 
    eapply corestep_plus_one. eapply rtl_corestep_exec_Itailcall; eauto.
    eapply sig_function_translated; eauto.
    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
     
    
    unfold MATCH.
    intuition.
    econstructor; eauto.
    eapply match_stacks_bound with (bound := sp'). 
    eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.nextblock_free; eauto. red in VB; xomega.
    eapply agree_val_regs; eauto.
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
    eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    eapply REACH_closed_free; eauto.
      (* sm_valid mu m1' m2' *)
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H7; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H7; assumption.
      (*  Mem.inject (as_inj mu) m1' m2' *)
      eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
      (* show that no valid location points into the stack block being freed *)
      intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
      eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega. 
      apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

    (* turned into a call *)
    eexists. eexists. split; simpl.
    left. 
    eapply corestep_plus_one. eapply rtl_corestep_exec_Icall; eauto.
    eapply sig_function_translated; eauto.
    
    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    econstructor; eauto.
    eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_invariant; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    eapply agree_val_regs; eauto.
    eapply Mem.free_left_inject; eauto.
    eapply REACH_closed_free; eauto.
    
    (*  sm_valid mu m1' m2 *)
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H7; assumption.
      eapply H7; assumption.
      (*  Mem.inject (as_inj mu) m1' m2' *)
      eapply Mem.free_left_inject; eauto.

    (* inlined *)
    assert (fd = Internal f0).
    simpl in H1. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat SrcProg); eauto. intros. 
    unfold ge in H1. congruence.
    subst fd.
    eexists. eexists.
    split; simpl.
    right; split. simpl; omega. 
    eapply corestep_star_zero.

    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
    intuition.
    econstructor; eauto.
    eapply match_stacks_inside_inlined_tailcall; eauto.
    eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    apply agree_val_regs_gen; auto.
    eapply Mem.free_left_inject; eauto.
    red; intros; apply PRIV'. 
    assert (dstk ctx <= dstk ctx'). red in H15; rewrite H15. apply align_le. apply min_alignment_pos.
    omega.
    eapply REACH_closed_free; eauto.
    (* sm_valid mu m1' m2 *)
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H11; assumption.
      eapply H11; assumption.
      (*  Mem.inject (as_inj mu) m1' m2' *)
      eapply Mem.free_left_inject; eauto.


    (* Icond *)

    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    assert (eval_condition cond rs'##(sregs ctx args) m2 = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto. 
    
    eexists. eexists. 
    split; simpl.
    left. 
    eapply corestep_plus_one.
    eapply rtl_corestep_exec_Icond; eauto.

    exists mu. intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    destruct b;
      econstructor; eauto.


    (* jumptable *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    assert (val_inject (as_inj mu) rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
    rewrite H1 in H3; inv H3.
    
    eexists. eexists.
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_Ijumptable; eauto.
    rewrite list_nth_z_map. rewrite H2. simpl; reflexivity. 
    
    exists mu. intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    econstructor; eauto.

    (* return *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.

    (* not inlined *)
    inv MS0; try congruence.
    assert (X: { m1' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
    destruct X as [m2' FREE].
    
    eexists. eexists.
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_Ireturn; eauto. 
    
    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
    intuition.
    econstructor; eauto.
    eapply match_stacks_bound with (bound := sp'). 
    eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.nextblock_free; eauto. red in VB; xomega.
    destruct or; simpl. apply agree_val_reg; auto. auto.

    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private (as_inj mu) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H16 in PRIV. eapply range_private_free_left; eauto. 
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
    eelim B; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

    eapply REACH_closed_free; eauto.

    (*  sm_valid mu m1' m2 *)
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H8; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H8; assumption.
      (*  Mem.inject (as_inj mu) m1' m2' *)
 eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private (as_inj mu) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H16 in PRIV. eapply range_private_free_left; eauto. 
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
    eelim B; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.


    (* inlined *)
    eexists. eexists.             
    split; simpl.
    right; split; simpl. omega.
    
    eapply corestep_star_zero.

    exists mu.
    intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve. 
    
    unfold MATCH;
    intuition.
    econstructor; eauto.
    
    
  eapply match_stacks_inside_invariant; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_left_inject; eauto.
  inv FB. subst.  rewrite H13 in PRIV. eapply range_private_free_left; eauto.
  
    eapply REACH_closed_free; eauto.
    (*sm_valid*)
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
      eapply H8; assumption.
      eapply H8; assumption.
      (*  Mem.inject (as_inj mu) m1' m2 *)
      eapply Mem.free_left_inject; eauto.

    (* internal function, not inlined *)
    assert (A: exists f', tr_function fenv f f' /\ fd' = Internal f'). 
    Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. 
    destruct A as [f' [TR EQ]]. inversion TR; subst.
    repeat open_Hyp.
    exploit alloc_parallel_intern; 
    eauto. apply Zle_refl. 
    instantiate (1 := fn_stacksize f'). inv H1. xomega.
    intros [mu' [m2' [sp' [A [B [C [D E]]]]]]].
    
    eexists. eexists.
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_function_internal; eauto.

    rewrite H5.
    exists mu'. 
    intuition.

    unfold MATCH; intuition.
    rewrite H6.
    rewrite <- H5.
    eapply match_regular_states.
    apply match_stacks_inside_base.
  assert (SP: sp' = Mem.nextblock m2) by (eapply Mem.alloc_result; eauto).
  rewrite <- SP in MS0. 
  eapply (match_stacks_invariant mu); eauto.
    eapply intern_incr_as_inj; eauto.
    intros. destruct (eq_block b1 stk). 
    subst b1. rewrite D in H20; inv H20. subst b2. eelim Plt_strict; eauto.  
    rewrite H14 in H20; auto. 
    intros. exploit Mem.perm_alloc_inv. eexact H0. eauto. 
    destruct (eq_block b1 stk); intros; auto. 
    subst b1. rewrite D in H20; inv H20. subst b2. eelim Plt_strict; eauto.  
    intros. eapply Mem.perm_alloc_1; eauto. 
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto. 
    rewrite dec_eq_false; auto.
  auto. auto. auto. 
  rewrite H5. apply agree_regs_init_regs.
  eapply val_list_inject_incr.
  Lemma inject_incr_structure: forall mu mu' (II: intern_incr mu mu'), inject_incr (as_inj mu) (as_inj mu').
  Admitted.
  eapply inject_incr_structure; eauto.
  eauto.
  auto. inv H1; auto. congruence. auto.
  eapply Mem.valid_new_block; eauto.
  red; intros. split.
  eapply Mem.perm_alloc_2; eauto. inv H1; xomega.
  intros; red; intros. exploit Mem.perm_alloc_inv. eexact H0. eauto.
  destruct (eq_block b stk); intros. 
  subst. rewrite D in H21; inv H21. inv H1; xomega.
  rewrite H14 in H21; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. omega.

  (* meminj_preserves_globals ge (as_inj mu') 
  unfold meminj_preserves_globals in H9.
   destruct H9 as [A' [B' C']].
   unfold meminj_preserves_globals; intros. 
   repeat split; intros.
   destruct (eq_block b stk); intros. 
   subst b. 
   rewrite D.*)
   
  admit.
  admit.


    (* internal function, inlined *)
    inversion FB; subst.
    exploit Mem.alloc_left_mapped_inject. 
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. xomega.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. xomega.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    intros [F' [A [B [C D]]]].
    exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
    eexists. eexists.
    split; simpl. 
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_Inop; eauto. 
    Print star.
    (* eexact P. traceEq.
  eapply match_regular_states.
  econstructor.
  eapply match_stacks_inside_alloc_left; eauto.
  eapply match_stacks_inside_invariant; eauto.
  omega.
  auto.
  apply agree_regs_incr with F; auto.
  auto. auto. auto.
  rewrite H2. eapply range_private_alloc_left; eauto.
  auto. auto.*)
    clear P. admit.
    

    (* external function *)
    (*  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  (*exploit external_call_mem_inject; eauto.
    eapply match_globalenvs_preserves_globals; eauto.
    Check external_call.
    Print extcall_sem. 
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].*)
  simpl in FD. inv FD. 
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    exact symbols_preserved. exact varinfo_preserved.
  econstructor.
    eapply match_stacks_bound with (Mem.nextblock m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto. 
    intros; eapply external_call_max_perm; eauto.
    xomega.
    eapply external_call_nextblock; eauto. 
    auto. auto.*)

    (* return fron noninlined function *)
    inv MS0.
    (* normal case *)
    eexists. eexists.
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_return.
    
    exists mu. intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH; intuition.
    econstructor; eauto. 
    apply match_stacks_inside_set_reg; auto. 
    apply agree_set_reg; auto.
    
    (* untailcall case *)
    inv MS; try congruence.
    rewrite RET in RET0; inv RET0.
    (*
  assert (rpc = pc). unfold spc in H0; unfold node in *; xomega.
  assert (res0 = res). unfold sreg in H1; unfold reg in *; xomega.
  subst rpc res0.
     *)
    eexists. eexists.     
    split; simpl.
    left.
    eapply corestep_plus_one. eapply rtl_corestep_exec_return.
    exists mu. intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH. intuition.
    eapply match_regular_states. 
    eapply match_stacks_inside_set_reg; eauto.
    auto. 
    apply agree_set_reg; auto.
    auto. auto. auto.
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.
    auto. auto. 
    
    (* return from inlined function *)
    inv MS0; try congruence. rewrite RET0 in RET; inv RET. 
    unfold inline_return in AT. 
    assert (PRIV': range_private (as_inj mu) m1' m2 sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega.
    (* with a result *)
    destruct or.
    eexists. eexists.
    split; simpl.
    left. 
    eapply corestep_plus_one.
    eapply rtl_corestep_exec_Iop; eauto. simpl. reflexivity.
    
    exists mu. intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH; intuition.
    econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
    (* without a result *)
    eexists. eexists.
    split; simpl. left.  
    eapply corestep_plus_one. eapply rtl_corestep_exec_Inop; eauto.
    exists mu. intuition.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b0;
    rewrite freshloc_irrefl;
    intuition.
    unfold MATCH; intuition.
    econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
  Qed.