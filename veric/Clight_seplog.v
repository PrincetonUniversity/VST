Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.

Require Export VST.veric.seplog.

Require Export VST.veric.mapsto_memory_block.

Local Open Scope pred.

Require Import compcert.cfrontend.Clight. 
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.binop_lemmas2.
Require Export VST.veric.Clight_mapsto_memory_block.

Local Open Scope pred.

(*Definition expr_true (e: Clight.expr) (rho: environ): Prop :=
  bool_val (eval_expr e rho) (Clight.typeof e) = Some true.*)

Definition expr_true {CS: compspecs} e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false {CS: compspecs} e := lift1 (typed_false (typeof e)) (eval_expr e).

(*
Definition fun_assert:
  forall (fml: funsig) cc (A: TypeTree)
   (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap))
   (v: val) , pred rmap :=
  res_predicates.fun_assert.
*)
Definition eval_lvar (id: ident) (ty: type) (rho: environ) :=
 match Map.get (ve_of rho) id with
| Some (b, ty') => if eqb_type ty ty' then Vptr b Ptrofs.zero else Vundef
| None => Vundef
end.

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type) (rho: environ): mpred :=
  !! (sizeof (snd idt) <= Ptrofs.max_unsigned) &&
  (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

Definition stackframe_of {cs: compspecs} (f: Clight.function) : assert :=
  fold_right (fun P Q rho => P rho * Q rho) (fun rho => emp) (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

Lemma stackframe_of_eq : forall {cs: compspecs}, stackframe_of =
        fun f rho => fold_right sepcon emp (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
Proof.
  intros.
 extensionality f rho.
 unfold stackframe_of.
 forget (fn_vars f) as vl.
 induction vl; simpl; auto.
 rewrite IHvl; auto.
Qed.

(*
Definition stackframe_of (f: Clight.function) : assert :=
  fun rho => sepcon_list (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
*)

Lemma  subst_derives:
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => tc_vals (map (@snd _ _) formals) (map (fun xt => (eval_id (fst xt) rho)) formals).

(*This definition, and lemma close_precondition_i below, could be moved to general_seplog*)
Program Definition close_precondition (specparams bodyparams: list ident) (P: environ -> pred rmap) (rho: environ) : pred rmap :=
 fun phi =>
   exists ve', exists te',
   (forall n i j, nth_error specparams n = Some i -> 
                    nth_error bodyparams n = Some j ->
                     Map.get te' i = Map.get (te_of rho) j) /\
   app_pred (P (mkEnviron (ge_of rho) ve' te')) phi.
Next Obligation.
intros.
intro; intros.
destruct H0 as [ve' [te' [? ?]]]; exists ve',te'; split; auto.
eapply pred_hereditary; eauto.
Qed.

Program Definition gclose_precondition (bodyparams: list ident) 
    (P: genviron * list val -> pred rmap) (rho:environ) : pred rmap :=
 fun phi => exists vals,
   map (Map.get (te_of rho)) bodyparams = map Some vals /\
   app_pred (P (ge_of rho, vals)) phi.
Next Obligation.
intros.
intro; intros.
destruct H0 as [vals [? ?]]. exists vals; split; auto.
eapply pred_hereditary; eauto.
Qed. 

(*
Definition AUX (ids:list ident) (vals:list val) 
          (P: genviron * list val -> mpred): environ -> mpred :=
fun rho => andp (local (fun rho => map (Map.get (te_of rho)) ids = map Some vals) rho)
                 ( P (ge_of rho, vals)).

Definition cp (ids: list ident) (P: genviron * list val -> mpred): environ -> mpred :=
fun omega => exp (fun vals => AUX ids vals P omega).

Lemma cp_char l P: cp l P = close_precondition l P.
Proof. extensionality rho. apply pred_ext; unfold close_precondition. 
+ intros m [vals [PR HP]]. simpl.
  exists vals. split; trivial.
+ intros m [vals [PR HP]]; simpl. exists vals; split;assumption.
Qed.

Program Definition cp' (bodyparams: list ident) (P: genviron * list val -> mpred) (rho:environ): mpred :=
  exp (fun vals =>
   (andp (prop (map (Map.get (te_of rho)) bodyparams = map Some vals))
        (P (ge_of rho, vals)))).

Lemma cp_char' l P: cp' l P = close_precondition l P.
Proof. extensionality rho. apply pred_ext; unfold close_precondition. 
+ intros m [vals [PR HP]]. simpl. exists vals. split; assumption. 
+ intros m [vals [PR HP]]; simpl. exists vals; split;assumption.
Qed.

Lemma cp_elim': forall ids P
  (HH: forall (rho : environ) (vals : list val),
     P (ge_of rho, vals) |-- !! (forall v : val, In v vals -> v <> Vundef))
  rho,
Clight_seplog.cp' ids P rho
|-- P (ge_of rho, map (fun i : ident => eval_id i rho) ids).
Proof. intros. unfold cp'. intros u [vals [V U]]. simpl in V. 
  specialize (HH _ _ _ U). simpl in HH.
  assert (vals = map (fun i : ident => eval_id i rho) ids).
  { clear - HH V. generalize dependent vals.
    induction ids; destruct vals; simpl; intros; trivial; inv V.
    f_equal.
    + clear IHids. unfold eval_id. rewrite H0; trivial. 
    + apply IHids; trivial.
      intros. apply HH. right; trivial. }
  subst; trivial.
Qed.*)

Definition precondition_closed (fs: list (ident*type)) {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred) : Prop :=
 forall ts x,
  closed_wrt_vars (not_a_param fs) (P ts x) /\
  closed_wrt_lvars (fun _ => True) (P ts x).

Lemma close_precondition_e:
   forall al (A: TypeTree) (P:  forall ts, dependent_type_functor_rec ts (AssertTT A) mpred),
    precondition_closed al P ->
  forall ts x rho,
   close_precondition (map fst al) (map fst al)  (P ts x) rho |-- P ts x rho.
Proof.
intros.
intros ? ?.
destruct H0 as [ve' [te' [? ?]]].
destruct (H ts x).
rewrite (H2 _ te').
rewrite (H3 _ ve').
simpl.
apply H1.
intros.
simpl; auto.
intros.
unfold not_a_param.
destruct (In_dec ident_eq i (map (@fst _ _) al)); auto.
right; symmetry.
destruct (In_nth_error _ _ i0) as [n ?].
apply (H0 _ _ _ H4 H4).
Qed.

Lemma close_precondition_e':
   forall al (P:  environ-> pred rmap),
   closed_wrt_vars (fun i => ~ In i al) P  ->
   closed_wrt_lvars (fun _ => True) P ->
   forall rho, close_precondition al al P rho |-- P rho.
Proof.
intros.
intros ? ?.
destruct H1 as [ve' [te' [? ?]]].
hnf in H,H0.
rewrite (H0 rho ve') by auto. clear H0.
rewrite (H _ te'); auto.
intros.
destruct (In_dec ident_eq i al); auto.
right; symmetry.
destruct (In_nth_error _ _ i0) as [n ?].
eapply H1; eauto.
Qed.

Lemma gclose_precondition_e':
   forall al (P: genviron * list val -> pred rmap) (rho: environ) ,
   gclose_precondition al P rho |-- 
   exp (fun vals =>
   !!(map (Map.get (te_of rho)) al = map Some vals) &&
   P (ge_of rho, vals)).
Proof. intros. intros u p. simpl in p. simpl; trivial. Qed.

(*
Definition bind_args (specparams bodyparams: list (ident * type)) (P: environ -> pred rmap) : assert :=
          fun rho => !! tc_formals bodyparams rho 
                          && close_precondition (map fst specparams) (map fst bodyparams) P rho.*)

Definition gbind_args (bodyparams: list (ident * type)) (P: genviron * list val -> pred rmap) : assert :=
  fun rho => !! tc_formals bodyparams rho 
     && gclose_precondition (map fst bodyparams) P rho.

Definition ret_temp : ident := 1%positive.

Definition get_result1 (ret: ident) (rho: environ) : environ :=
   make_args (ret_temp::nil) (eval_id ret rho :: nil) rho.

Definition get_result (ret: option ident) : environ -> environ :=
 match ret with
 | None => make_args nil nil
 | Some x => get_result1 x
 end.

Definition bind_ret (vl: option val) (t: type) (Q: assert) : assert :=
     match vl, t with
     | None, Tvoid => fun rho => Q (make_args nil nil rho)
     | Some v, _ => fun rho => !! (tc_val t v) &&
                               Q (make_args (ret_temp::nil) (v::nil) rho)
     | _, _ => fun rho => FF
     end.

Definition gbind_ret (vl: option val) (t: type) (Q: gassert) : assert :=
     match vl, t with
     | None, Tvoid => fun rho => Q (ge_of rho, nil)
     | Some v, _ => fun rho => !! (tc_val t v) &&
                               Q (ge_of rho, cons v nil)
     | _, _ => fun rho => FF
     end.

Definition funassert (Delta: tycontext): assert := funspecs_assert (glob_specs Delta).

(* Unfortunately, we need core_load in the interface as well as address_mapsto,
  because the converse of 'mapsto_core_load' lemma is not true.  The reason is
  that core_load could imply partial ownership of the four bytes of the word
  using different shares that don't have a common core, whereas address_mapsto
  requires the same share on all four bytes. *)
(*
Record ret_assert : Type := {
 RA_normal: assert;
 RA_break: assert;
 RA_continue: assert;
 RA_return: option val -> assert
}.
*)
Definition proj_ret_assert (Q: ret_assert) (ek: exitkind) (vl: option val) : assert :=
 match ek with
 | EK_normal => fun rho => !! (vl=None) && RA_normal Q rho
 | EK_break => fun rho => !! (vl=None) && RA_break Q rho
 | EK_continue => fun rho => !! (vl=None) && RA_continue Q rho
 | EK_return => RA_return Q vl
 end.

(* Definition ret_assert := exitkind -> option val -> assert. *)

Definition overridePost  (Q: assert)  (R: ret_assert) :=
 match R with 
  {| RA_normal := _; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Q; RA_break := b; RA_continue := c; RA_return := r |}
 end.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) :=
  {| RA_normal := fun rho => EX x:A, (R x).(RA_normal) rho;
     RA_break := fun rho => EX x:A, (R x).(RA_break) rho;
     RA_continue := fun rho => EX x:A, (R x).(RA_continue) rho;
     RA_return := fun vl rho => EX x:A, (R x).(RA_return) vl rho
   |}.

Definition normal_ret_assert (Q: assert) : ret_assert :=
  {| RA_normal := Q; RA_break := seplog.FF; RA_continue := seplog.FF; RA_return := fun _ => seplog.FF |}.

Definition frame_ret_assert (R: ret_assert) (F: assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := fun rho => n rho * F rho; 
     RA_break := fun rho => b rho * F rho; 
     RA_continue := fun rho => c rho * F rho;
     RA_return := fun vl rho => r vl rho * F rho |}
 end.

Definition conj_ret_assert (R: ret_assert) (F: assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := fun rho => n rho && F rho; 
     RA_break := fun rho => b rho && F rho; 
     RA_continue := fun rho => c rho && F rho;
     RA_return := fun vl rho => r vl rho && F rho |}
 end.

Definition switch_ret_assert (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := seplog.FF; 
     RA_break := n; 
     RA_continue := c;
     RA_return := r |}
 end.

Require Import VST.msl.normalize.

Lemma normal_ret_assert_derives:
 forall P Q rho,
  P rho |-- Q rho ->
  forall ek vl, proj_ret_assert (normal_ret_assert P) ek vl rho 
            |-- proj_ret_assert (normal_ret_assert Q) ek vl rho.
Proof.
 intros.
 destruct ek; simpl; normalize.
Qed.
Hint Resolve normal_ret_assert_derives : core.

Lemma normal_ret_assert_FF:
  forall ek vl rho, proj_ret_assert (normal_ret_assert (fun rho => FF)) ek vl rho = FF.
Proof.
intros.
destruct ek; simpl; normalize.
Qed.

Lemma frame_normal:
  forall P F,
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (fun rho => P rho * F rho).
Proof.
intros.
unfold normal_ret_assert; simpl.
f_equal; simpl; try solve [extensionality rho; normalize].
extensionality vl rho; normalize.
Qed.

Lemma proj_frame:
  forall P F ek vl,
    proj_ret_assert (frame_ret_assert P F) ek vl = fun rho => F rho * proj_ret_assert P ek vl rho.
Proof.
  intros.
  extensionality rho.
  rewrite sepcon_comm.
  destruct ek; simpl; destruct P; auto;
  normalize.
Qed.

Lemma proj_conj:
  forall P F ek vl,
    proj_ret_assert (conj_ret_assert P F) ek vl = fun rho => F rho && proj_ret_assert P ek vl rho.
Proof.
  intros.
  extensionality rho.
  rewrite andp_comm.
  destruct ek; simpl; destruct P; auto; simpl; normalize; rewrite andp_assoc; auto.
Qed.

Definition loop1_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := Inv;
     RA_return := r |}
 end.

Definition loop2_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n;
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Lemma frame_for1:
  forall Q R F,
   frame_ret_assert (loop1_ret_assert Q R) F =
   loop1_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; auto.
Qed.

Lemma frame_loop1:
  forall Q R F,
   frame_ret_assert (loop2_ret_assert Q R) F =
   loop2_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
destruct R; simpl; auto.
f_equal; extensionality; normalize.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
f_equal.
Qed.

Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_loop1
                 overridePost_normal: normalize.

Definition function_body_ret_assert (ret: type) (Q: assert) : ret_assert :=
 {| RA_normal := bind_ret None ret Q;
    RA_break := seplog.FF; 
    RA_continue := seplog.FF;
    RA_return := fun vl => bind_ret vl ret Q |}.

Definition gfunction_body_ret_assert (ret: type) (Q: gassert) : ret_assert :=
 {| RA_normal := gbind_ret None ret Q;
    RA_break := seplog.FF; 
    RA_continue := seplog.FF;
    RA_return := fun vl => gbind_ret vl ret Q |}.

Lemma same_glob_funassert:
  forall Delta1 Delta2,
     (forall id, (glob_specs Delta1) ! id = (glob_specs Delta2) ! id) ->
              funassert Delta1 = funassert Delta2.
Proof. intros; eapply same_FS_funspecs_assert; trivial. Qed.

(**************** CONVERSION BETWEEN AssertTT and ArgsTT predicates **************)

Lemma get_make_args' {x}: forall {ids vals n} (LNR: list_norepet ids)
      (L:length ids = length vals) (Hx: nth_error ids n = Some x),
      Map.get (make_args' ids vals) x = nth_error vals n.
Proof.
  induction ids; intros; destruct vals; inv L; inv LNR; simpl.
+ rewrite nth_error_nil in Hx; discriminate.
+ destruct n; simpl in *.
  - inv Hx. apply Map.gss.
  - rewrite Map.gso. auto.
    intros N; subst. apply nth_error_In in Hx. congruence.
Qed.

Lemma make_context_t_get: forall {params temps i ty} 
      (T: (make_tycontext_t params temps) ! i = Some ty),
      In i (map fst params ++ map fst temps).
Proof.
  induction params; simpl; intros.
* induction temps; simpl in *. rewrite PTree.gempty in T; discriminate. 
  destruct a; simpl in *. rewrite PTree.gsspec in T.
  destruct (peq i i0); subst. left; trivial. right; auto.
* destruct a; simpl in *. rewrite PTree.gsspec in T.
  destruct (peq i i0); subst. left; trivial.
  right. eapply IHparams. apply T.
Qed.

Lemma tc_temp_environ_elim: forall {params temps trho},
      list_norepet (map fst params ++ map fst temps) ->
      typecheck_temp_environ trho (make_tycontext_t params temps) ->
      forall i ty, In (i,ty) params -> 
      exists v : val, Map.get trho i = Some v /\ tc_val' ty v.
Proof.
  induction params.
  + intros. inv H1.
  + simpl. intros. destruct H1.
    - subst a. simpl in *. apply (H0 i ty). rewrite PTree.gss; trivial.
    - inv H. apply (IHparams temps); trivial.
      red; intros j ? ?. apply H0. rewrite PTree.gso; trivial. clear - H4 H.
      intros J; subst. destruct a; simpl in *. apply H4; clear - H.
      apply (make_context_t_get H).
Qed.

Definition mkEnv g ids vals : environ := 
      make_args ids vals (mkEnviron g (Map.empty (block * type)) (Map.empty val)).

(*NEW*) Definition assert2gassert (ids: list ident) (M:assert):gassert :=
fun gv => M (mkEnv (fst gv) ids (snd gv)).

Definition ArgsTT2AssertTT {A} (ids:list ident) (P: forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (ArgsTT A)) mpred) :
       forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (AssertTT A)) mpred.
Proof. intros ts M rho. apply (P ts M (ge_of rho, map (fun i => eval_id i rho) ids)). Defined.

Definition AssertTT2ArgsTT {A} (ids:list ident) (P: forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (AssertTT A)) mpred):
        forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (ArgsTT A)) mpred.
Proof. intros ts M x. apply (match x with (g, vals) => P ts M (mkEnv g ids vals) end). Defined.
(*
Definition ArgsTT2AssertTT {A} (ids:list ident) (P: forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (ArgsTT A)) mpred) :
       forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (AssertTT A)) mpred :=
fun ts M rho => P ts M (ge_of rho, map (fun i => eval_id i rho) ids).

Definition AssertTT2ArgsTT {A} (ids:list ident) (P: forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (AssertTT A)) mpred):
        forall ts : list Type,
                        functors.MixVariantFunctor._functor
                          (rmaps.dependent_type_functor_rec ts
                             (ArgsTT A)) mpred :=
fun ts M x => match x with (g, vals) => P ts M (mkEnv g ids vals) end.
*)

Definition i2o (phi: funspec):Newfunspec.
destruct phi as [[params rt] c A P Q P_ne Q_ne].
apply (mk_Newfunspec (map snd params, rt) c A
                   (AssertTT2ArgsTT (map fst params) P)
                   (AssertTT2ArgsTT (cons ret_temp nil) Q)).
red; intros. destruct gargs as [g vals]. apply P_ne.
red; intros. destruct gargs as [g vals]. apply Q_ne.
Defined.

Definition o2i (phi: Newfunspec) (ids: list ident):funspec.
destruct phi as [[types rt] c A P Q P_ne Q_ne].
apply (mk_funspec (combine ids types, rt) c A 
                    (ArgsTT2AssertTT ids P) 
                    (ArgsTT2AssertTT (match rt with
                                         Tvoid => nil
                                       |  _ => cons ret_temp nil
                                      end) Q)).
red; intros. apply P_ne.
red; intros. apply Q_ne.
Defined.

Lemma cp_o2i {A P ts x l ids rho} (LNR:list_norepet l) (LEN: length l = length ids):
    gclose_precondition ids (@AssertTT2ArgsTT A l P ts x) rho
|-- close_precondition l ids (P ts x) rho.
Proof.
  intros m [args [Args M]]. simpl in M. unfold mkEnv in M.
  exists (Map.empty (block * type)), (make_args' l args).
  assert (LENArgs: length l = length args).
  { assert (length (map (Map.get (te_of rho)) ids) = length (map Some args)) by (rewrite Args; trivial).
    rewrite 2 map_length in H. rewrite LEN; apply H. }
  rewrite make_args_eq in M by trivial. simpl in M. split; trivial.
  intros. erewrite get_make_args'; trivial. 2: apply H.
  clear M P.
    specialize (map_nth_error (Map.get (te_of rho)) n ids H0); clear H0.
    rewrite Args; intros.
    rewrite list_map_nth in H0; unfold option_map in H0.
    destruct (nth_error args n); inv H0; trivial.
Qed.

Lemma cp_i2o_aux {P l params temps rho}
  (LEN : Datatypes.length l = Datatypes.length params)
  (LNRf : list_norepet (map fst params ++ map fst temps))
  (TC : typecheck_temp_environ (te_of rho)
        (make_tycontext_t params temps)):
close_precondition l (map fst params)
  (fun tau => P (ge_of tau, map (fun i => eval_id i tau) l)) rho
|-- gclose_precondition (map fst params) P rho.
Proof.
    intros m [ve' [te' [HH M]]]. 
    red. simpl. simpl in M.
    exists (map (fun i : ident => eval_id i (mkEnviron (ge_of rho) ve' te')) l).
    split; [ clear M | trivial].
    clear - LEN HH TC LNRf. 
    assert (L: length l = length (map fst params)).
    { rewrite LEN,  map_length; trivial. } unfold eval_id; simpl.
    specialize (tc_temp_environ_elim LNRf TC); clear TC; intros TC.
    clear - HH L TC.
    generalize dependent params. induction l; destruct params; simpl; intros; trivial; inv L.
    destruct p as [pi pt]; simpl in *.
    rewrite IHl; clear IHl; trivial.
    - f_equal.
      rewrite (HH O a pi); trivial.
      destruct (TC pi pt) as [v [HV V]]. left; trivial.
      rewrite HV; trivial.
    - intros. apply (HH (S n)); trivial.
    - intros. apply TC. right; trivial.
Qed.

Lemma cp_i2o {A P ts x l params temps rho}
  (LEN : Datatypes.length l = Datatypes.length params)
  (LNRf : list_norepet (map fst params ++ map fst temps))
  (TC : typecheck_temp_environ (te_of rho)
        (make_tycontext_t params temps)):
  close_precondition l (map fst params)
        (@ArgsTT2AssertTT A l P ts x) rho
|-- gclose_precondition (map fst params) (P ts x) rho.
Proof. eapply cp_i2o_aux; eassumption. Qed.

Lemma gclose_gassert al P rho: gclose_precondition al P rho |-- 
      (!!(map (Map.get (te_of rho)) al = map Some (map (fun i => eval_id i rho) al)) 
          && gassert2assert al P rho).
Proof. unfold gclose_precondition, gassert2assert. intros u [vals [U1 U2]].
assert (vals = map (fun i : ident => eval_id i rho) al).
{ clear -U1. generalize dependent vals.
  induction al; simpl; intros; destruct vals; inv U1; trivial.
  rewrite (IHal _ H1). f_equal. unfold eval_id; rewrite H0. simpl; trivial. }
  simpl in U1.
rewrite <- H. split; trivial.
Qed.

Lemma gclose_gassert_inv al P rho: 
  (!!(map (Map.get (te_of rho)) al = map Some (map (fun i => eval_id i rho) al)) 
   && gassert2assert al P rho)
 |-- gclose_precondition al P rho.
Proof. unfold gclose_precondition, gassert2assert. intros u [U1 U2].
exists (map (fun i : ident => eval_id i rho) al). split; trivial.
Qed.
