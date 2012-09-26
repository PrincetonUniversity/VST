Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
Require Import veric.initial_world.
Require Import msl.normalize.
Require Import veric.seplog_soundness.

Open Local Scope pred.

Section semax_prog.
Context {Z} (Hspec: juicy_ext_spec Z).

Definition prog_contains (ge: genv) (fdecs : list (ident * fundef)) : Prop :=
     forall id f, In (id,f) fdecs -> 
         exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some f.

Definition entry_tempenv (te: temp_env) (f: function) (vl: list val) :=
   length vl = length f.(fn_params) /\
   forall id v, PTree.get id te = Some v ->  
                      In (id,v) 
                       (combine (map (@fst _ _) f.(fn_params)) vl 
                          ++ map (fun tv => (fst tv, Vundef)) f.(fn_temps)).

Definition semax_body_params_ok f : bool :=
   andb 
        (compute_list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)))
        (compute_list_norepet (map (@fst _ _) (fn_vars f))).


Definition semax_body
       (G: funspecs) (f: function) (A: Type) (P Q: A -> assert) : Prop :=
  forall x,
      semax Hspec (func_tycontext f) G
          (fun rho => bind_args (fn_params f) (P x) rho *  stackframe_of f rho)
          f.(fn_body)
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f)).

Definition match_fdecs (fdecs: list (ident * fundef)) (G: funspecs) :=
 map (fun idf => (fst idf, Clight.type_of_fundef (snd idf))) fdecs = 
 map (fun idf => (fst idf, type_of_funspec (snd idf))) G.

Definition semax_func
        (G: funspecs) (fdecs: list (ident * fundef)) (G1: funspecs) : Prop :=
   match_fdecs fdecs G1 /\
  forall ge, prog_contains ge fdecs -> 
          forall n, believe Hspec G ge G1 n.

Definition main_pre (prog: program) : unit -> assert :=
(fun tt vl => writable_blocks (map (initblocksize type) prog.(prog_vars)) 
                             (empty_environ (Genv.globalenv prog))).

Definition Tint32s := Tint I32 Signed noattr.

Definition main_post (prog: program) : unit -> assert := 
  (fun tt _ => TT).

Definition semax_prog 
     (prog: program) (G: funspecs) : Prop :=
  compute_list_norepet (map (@fst _ _) prog.(prog_funct)
                                       ++ map (@fst _ _) prog.(prog_vars)) = true  /\
  semax_func G (prog.(prog_funct)) G /\
    In (prog.(prog_main), mk_funspec (nil,Tvoid) unit (main_pre prog ) (main_post prog)) G.

Lemma semax_func_nil: 
   forall
     G, semax_func G nil nil.
Proof.
intros; split; auto.
hnf; auto.
intros.
intros b fsig ty P Q w ? ?.
hnf in H1.
destruct H1 as [b' [? ?]]. inv H1.
Qed.

Program Definition HO_pred_eq {T}{agT: ageable T}
    (A: Type) (P: A -> pred T) (A': Type) (P': A' -> pred T) : pred nat :=
 fun v => exists H: A=A', 
     match H in (_ = A) return (A -> pred T) -> Prop with
     | refl_equal => fun (u3: A -> pred T) =>
                                    forall x: A, (P x <=> u3 x) v
     end P'.
 Next Obligation.
  intros; intro; intros.
  destruct H0. exists x.
  destruct x. 
   intros. specialize (H0 x). eapply pred_hereditary; eauto.
 Qed.

Lemma approx_oo_approx'':
   forall n n' : nat,
  (n' >= n)%nat ->
    approx n' oo approx n = approx n.
Proof.
intros.
extensionality P.
apply pred_ext'; extensionality w.
unfold approx, compose.
simpl. rewrite rmap_level_eq.
case_eq (unsquash w); intros; simpl in *.
apply prop_ext; intuition.
Qed.

Lemma laterR_level: forall w w' : rmap, laterR w w' -> (level w > level w')%nat.
Proof.
induction 1.
unfold age in H. rewrite <- ageN1 in H.
change rmap with R.rmap; change ag_rmap with R.ag_rmap.
rewrite (ageN_level _ _ _ H). generalize (@level _ R.ag_rmap y). intros; omega.
omega.
Qed.

Lemma necR_level:  forall w w' : rmap, necR w w' -> (level w >= level w')%nat.
Proof.
induction 1.
unfold age in H. rewrite <- ageN1 in H.
change rmap with R.rmap; change ag_rmap with R.ag_rmap.
rewrite (ageN_level _ _ _ H). generalize (@level _ R.ag_rmap y). intros; omega.
omega.
omega.
Qed.

Lemma HO_pred_eq_i1:
  forall A P P' m, 
      approx (level m) oo  P = approx (level m) oo P' ->
    (|> HO_pred_eq A P A  P') m.
Proof.
intros.
unfold HO_pred_eq.
intros ?m ?.
hnf.
exists (refl_equal A).
intros.
generalize (f_equal (fun f => f x) H); clear H; intro.
simpl in H0.
unfold compose in *.
apply clos_trans_t1n in H0.
revert H; induction H0; intros.
Focus 2. apply IHclos_trans_1n.
unfold age,age1 in H. unfold ag_nat in H. unfold natAge1 in H. destruct x0; inv H.
clear - H1.
assert (forall w, app_pred (approx (level (S y)) (P x)) w <-> app_pred (approx (level (S y)) (P' x)) w).
intros; rewrite H1; intuition.
apply pred_ext; intros w ?; destruct (H w); simpl in *; intuition.
apply H0; auto. clear - H4.  unfold natLevel in *. omega.
apply H2; auto. clear - H4.  unfold natLevel in *. omega.
(* End Focus 2 *)
unfold age,age1 in H. unfold ag_nat in H. unfold natAge1 in H. destruct x0; inv H.
intros z ?.
split; intros ? ? ?.
assert (app_pred (approx (level (S y)) (P x)) a').
simpl. split; auto. unfold natLevel.  apply necR_level in H1.
change compcert_rmaps.R.rmap with rmap in *.
change compcert_rmaps.R.ag_rmap with ag_rmap in *.
omega.
rewrite H0 in H3.
simpl in H3. destruct H3; auto.
assert (app_pred (approx (level (S y)) (P' x)) a').
simpl. split; auto. unfold natLevel.  apply necR_level in H1.
change compcert_rmaps.R.rmap with rmap in *.
change compcert_rmaps.R.ag_rmap with ag_rmap in *.
omega.
rewrite <- H0 in H3.
simpl in H3. destruct H3; auto.
Qed.

Lemma fst_match_fdecs:
 forall {fs G}, match_fdecs fs G -> map (@fst _ _) fs = map (@fst _ _) G.
Proof.
induction fs; destruct G; simpl; intros; inv H; simpl; auto.
f_equal; auto.
Qed.

Lemma in_map_fst: forall {A B: Type} (i: A) (j: B) (G: list (A*B)), 
  In (i,j) G -> In i (map (@fst _ _ ) G).
Proof.
 induction G; simpl; intros; auto.
 destruct H; [left|right]. subst; simpl; auto. auto.
Qed.
Require Import JMeq.

Lemma semax_func_cons_aux:
  forall (psi: genv) id fsig1 A1 P1 Q1 fsig2 A2 P2 Q2 (G': funspecs) b fs,
  Genv.find_symbol psi id = Some b ->
  ~ In id (map (fst (A:=ident) (B:=fundef)) fs) ->
   match_fdecs fs G'  ->
   claims  psi ((id, mk_funspec fsig1 A1 P1 Q1) :: G') (Vptr b Int.zero) fsig2 A2 P2 Q2 ->
    fsig1=fsig2 /\ A1=A2 /\ JMeq P1 P2 /\ JMeq Q1 Q2.
Proof.
intros until 1; intros (*Hok*) Hin (* Had *) Hmf; intros.
destruct H0 as [id' [? ?]].
simpl in H0.
destruct H0.
inv H0.
apply inj_pair2 in H6. apply inj_pair2 in H7.
subst.
split; auto.
elimtype False.
destruct H1 as [b' [? ?]].
symmetry in H2; inv H2.
assert (In id' (map (@fst _ _) G')).
clear - H0.
revert H0; induction G'; simpl; intros; auto.
destruct H0; [left | right]; auto.
destruct a; simpl in *; inv H; auto.
destruct (eq_dec id id').
2: apply (Genv.global_addresses_distinct psi n H H1); auto.
subst id'.
clear - Hin H2 Hmf.
rewrite (fst_match_fdecs Hmf) in Hin; contradiction.
Qed.

Lemma semax_func_cons: 
   forall 
         fs id f A P Q (G G': funspecs),
      andb (id_in_list id (map (@fst _ _) G)) 
      (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
        (semax_body_params_ok f)) = true ->
      semax_body G f A P Q ->
      semax_func G fs G' ->
      semax_func G ((id, Internal f)::fs) 
           ((id, mk_funspec (fn_funsig f) A P Q)  :: G').
Proof.
intros until G'.
intros H' H3 [Hf' Hf].
apply andb_true_iff in H'.
destruct H' as [Hin H'].
apply andb_true_iff in H'.
destruct H' as [Hni H].
split.
hnf.
simpl; f_equal; auto.
intros ge H0 n.
assert (prog_contains ge fs).
unfold prog_contains in *.
intros.
apply H0.
simpl.
auto.
spec Hf ge H1.
clear H1.
hnf in Hf|-*.
intros v fsig A' P' Q'.
apply derives_imp.
clear n.
intros n ?.
spec H0 id (Internal f).
destruct H0 as [b [? ?]].
left; auto.
rewrite <- Genv.find_funct_find_funct_ptr in H2.
apply negb_true_iff in Hni.
apply id_in_list_false in Hni.
destruct (eq_dec  (Vptr b Int.zero) v) as [?H|?H].
(* Vptr b Int.zero = v *)
subst v.
right.
exists b; exists f.
split.
apply andb_true_iff in H.
destruct H as [H H'].
apply compute_list_norepet_e in H.
apply compute_list_norepet_e in H'.
split3; auto.
rewrite Genv.find_funct_find_funct_ptr in H2; auto.
split; auto.
split; auto.
destruct H1 as [id' [? [b' [? ?]]]].
symmetry in H5; inv H5.
destruct (eq_dec id id').
subst.
simpl in H1.
destruct H1.
inv H1; auto.
elimtype False.
clear - Hf' Hni H1.
rewrite (fst_match_fdecs Hf') in Hni.
apply in_map_fst in H1; auto.
contradiction (Genv.global_addresses_distinct ge n0 H0 H4); auto.
destruct H.
intro x.
simpl in H1.
pose proof (semax_func_cons_aux ge _ _ _ _ _ _ _ _ _ _ _ _ H0 Hni Hf' H1).
destruct H as [H4' [H4 [H4b H4c]]].
subst A' fsig.
apply JMeq_eq in H4b.
apply JMeq_eq in H4c.
subst P' Q'.
specialize (H3 x).
rename H3 into H4.
pose proof I.
specialize (H4 n).
apply now_later.
clear - H4.
rewrite semax_fold_unfold in H4|-*.
revert n H4.
apply allp_derives; intro gx.
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply imp_derives; auto.
unfold guard.
apply allp_derives; intro rho.
eapply subp_derives; auto.
apply andp_derives; auto.
apply andp_derives; auto.
apply sepcon_derives; auto.
apply andp_left1; auto.
(***   Vptr b Int.zero <> v'  ********)
apply (Hf n v fsig A' P' Q'); auto.
destruct H1 as [id' [? ?]].
simpl in H1; destruct H1.
inv H1. destruct H5 as [? [? ?]]; congruence.
exists id'; split; auto.
Qed.

Lemma semax_func_cons_ext: 
   forall 
         (G: funspecs) fs id ef fsig A P Q (G': funspecs),
      andb (id_in_list id (map (@fst _ _) G))
              (negb (id_in_list id (map (@fst _ _) fs))) = true ->
      (forall n, semax_ext Hspec ef A P Q n) ->
      semax_func G fs G' ->
      semax_func G ((id, External ef (fst fsig) (snd fsig))::fs) 
           ((id, mk_funspec (arglist 1%positive (fst fsig), (snd fsig)) A P Q)  :: G').
Proof.
intros until G'.
intros H' H [Hf' Hf].
apply andb_true_iff in H'.
destruct H' as [Hin Hni].
apply id_in_list_true in Hin.
apply negb_true_iff in Hni; apply id_in_list_false in Hni.
split.
destruct fsig; hnf; simpl; f_equal; auto.
f_equal. f_equal.
clear; forget 1%positive as n.
revert n; induction t; simpl;intros; auto.
f_equal; auto.
intros ge; intros.
assert (prog_contains ge fs).
unfold prog_contains in *.
intros.
apply H0.
simpl.
auto.
specialize (Hf ge H1).
clear H1.
unfold believe.
intros v' fsig' A' P' Q'.
apply derives_imp.
clear n.
intros n ?.
unfold prog_contains in H0.
generalize (H0 id (External ef (fst fsig) (snd fsig))); clear H0; intro H0.
destruct H0 as [b [? ?]].
left; auto.
rewrite <- Genv.find_funct_find_funct_ptr in H2.
destruct (eq_dec  (Vptr b Int.zero) v') as [?H|?H].
subst v'.
left.
specialize (H n).
pose proof (semax_func_cons_aux ge _ _ _ _ _ _ _ _ _ _ _ _ H0 Hni Hf' H1).
destruct H3 as [H4' [H4 [H4b H4c]]].
subst A' fsig'.
apply JMeq_eq in H4b.
apply JMeq_eq in H4c.
subst P' Q'.
unfold believe_external.
rewrite H2.
split; auto.
hnf. auto.

(***   Vptr b Int.zero <> v'  ********)
apply (Hf n v' fsig' A' P' Q'); auto.
destruct H1 as [id' [? ?]].
simpl in H1; destruct H1.
inv H1. destruct H4 as [? [? ?]]; congruence.
exists id'; split; auto.
Qed.

Definition main_params (ge: genv) start : Prop :=
  exists b, exists func,
    Genv.find_symbol ge start = Some b /\
        Genv.find_funct ge (Vptr b Int.zero) = Some (Internal func) /\
        func.(fn_params) = nil.

Lemma in_prog_funct_negative:
 forall (prog: program) id b, 
  no_dups (prog_funct prog) (prog_vars prog) -> 
    In id (map (fst (A:=ident) (B:=fundef)) (prog_funct prog)) ->
             Genv.find_symbol (Genv.globalenv prog) id = Some b ->  b<0.
Proof.
intros.
assert (exists f, In (id,f) (prog_funct prog)).
remember (prog_funct prog) as l; clear - H0; induction l; simpl in *.
contradiction.
destruct a; destruct H0.
simpl in H; subst.
econstructor; left; eauto.
destruct (IHl H); econstructor; right; eauto.
destruct H2 as [f ?]. 
destruct (list_norepet_append_inv _ _ _ H) as [? [? ?]].
exploit (@Genv.find_funct_ptr_exists fundef _ prog id f); auto.
intros [b' [? ?]].
rewrite H1 in H6.
inv H6.
apply Genv.find_funct_ptr_negative with (p:=prog) (b:= b')(f:=f); 
auto.
Qed.

(*
Definition funcptr G v A P Q : assert :=
   (EX gm: env ident val, has_ge gm &&
       !((G && has_ge gm) >=> (TT * ^m fun_assert v Share.top A P Q))).

Lemma semax_prog_rule_aux3:
  forall G1 id sh A P Q st1 st2, 
          (fun_id id sh A P Q * G1)%pred st1 ->
          w_ge st1 = w_ge st2 ->
          exists v, (global_id id =# v) st2.
Proof.
intros.
destruct H as [w1 [w2 [? [? ?]]]].
destruct H1 as [v ?].
exists v.
unfold global_id.
rewrite <- world_op_con in H1.
rewrite sepcon_emp in H1.
destruct H1 as [? [_ ?]].
rewrite emp_sepcon in H3.
destruct H3 as [bb [? _]]. hnf in H3.  subst v.
destruct H as [? _].
rewrite H0 in H.
apply env_mapsto_get in H1; destruct H1.
assert (join_sub (w_ge w1) (w_ge st2)) by eauto with typeclass_instances.
destruct (env_get_join_sub _ _ _ _ _ H3 H1) as [? [? ?]].
econstructor.
eassumption.
rewrite Int.add_zero. auto.
Qed.
*)

Require Import veric.forward_simulations.

Fixpoint find_id (id: ident) (G: funspecs) : option funspec  :=
 match G with 
 | (id', f)::G' => if eq_dec id id' then Some f else find_id id G'
 | nil => None
 end.

Definition initial_core' (ge: Genv.t fundef type) (G: funspecs) (n: nat) (loc: address) : resource :=
   if eq_dec (snd loc) 0
   then match Genv.invert_symbol ge (fst loc) with
           | Some id => 
                  match find_id id G with
                  | Some (mk_funspec fsig A P Q) => 
                           PURE (FUN fsig) (SomeP (A::boolT::environ::nil) (approx n oo packPQ P Q))
                  | None => NO Share.bot
                  end
           | None => NO Share.bot
          end
   else NO Share.bot.

Program Definition initial_core (ge: Genv.t fundef type) (G: funspecs) (n: nat) : rmap :=
  proj1_sig (make_rmap (initial_core' ge G n) _ n _).
Next Obligation.
intros.
intros ? ?.
unfold compose.
unfold initial_core'.
if_tac; simpl; auto.
destruct (Genv.invert_symbol ge b); simpl; auto.
destruct (find_id i G); simpl; auto.
destruct f; simpl; auto.
Qed.
Next Obligation.
intros.
extensionality loc; unfold compose, initial_core'.
if_tac; [ | simpl; auto].
destruct (Genv.invert_symbol ge (fst loc)); [ | simpl; auto].
destruct (find_id i G); [ | simpl; auto].
destruct f.
unfold resource_fmap.
f_equal.
simpl.
change R.approx with approx.
rewrite <- compose_assoc.
 rewrite approx_oo_approx.
auto.
Qed.


Lemma initial_core_ok: forall (prog: program) G n, 
     no_dups (prog_funct prog) (prog_vars prog) ->
      match_fdecs (prog_funct prog) G ->
     initial_rmap_ok (initial_core (Genv.globalenv prog) G n).
Proof.
intros.
intros [b z] ?.
unfold initial_core; simpl.
rewrite <- core_resource_at.
rewrite resource_at_make_rmap.
unfold initial_core'.
simpl in *.
if_tac; [ | rewrite core_NO; auto].
case_eq (Genv.invert_symbol (Genv.globalenv prog) b); intros;  [ | rewrite core_NO; auto].
case_eq (find_id i G); intros; [ | rewrite core_NO; auto].
apply Genv.invert_find_symbol in H3.
apply in_prog_funct_negative in H3; auto.
contradiction.
forget (prog_funct prog) as fd.
clear - H0 H4.
revert fd H4 H0; induction G; simpl; intros. inv H4.
destruct a.
if_tac in H4.
subst i0.
inv H4.
destruct fd; inv H0.
left; auto.
destruct fd; inv H0.
right.
apply IHG; auto.
Qed.

Lemma find_id_i:
  forall id fs G, 
            In (id,fs) G ->
             list_norepet (map (@fst _ _) G) ->
                  find_id id G = Some fs.
Proof.
induction G; simpl; intros.
contradiction.
destruct H. subst. rewrite if_true; auto.
inv H0.
destruct a as [i j].
if_tac.
subst i.
simpl in *; f_equal.
apply in_map_fst in H. contradiction.
auto.
Qed.

Lemma find_id_e: 
   forall id G fs, find_id id G = Some fs -> In (id,fs) G.
Proof.
 induction G; simpl; intros. inv H. destruct a. if_tac in H.
 inv H; subst; auto. right; apply (IHG fs); auto.
Qed.

Lemma funassert_initial_core:
  forall prog ve te G n, 
     no_dups (prog_funct prog) (prog_vars prog) ->
      match_fdecs (prog_funct prog) G ->
      app_pred (funassert G (mkEnviron (filter_genv (Genv.globalenv prog)) ve te))
                      (initial_core (Genv.globalenv prog) G n).
Proof.
 intros; split.
 intros id fs.
 apply prop_imp_i; intros.
 simpl ge_of; simpl fst; simpl snd.
 unfold filter_genv.
 assert (exists f, In (id, f) (prog_funct prog)).
apply in_map_fst in H1. apply fst_match_fdecs in H0.
rewrite <- H0 in H1. forget (prog_funct prog) as g.
clear - H1.
induction g; simpl in *. contradiction. destruct H1.
subst. destruct a; simpl; eauto.
destruct (IHg H). eauto.
destruct H2 as [f ?].
 destruct (Genv.find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
 destruct (list_norepet_append_inv _ _ _ H) as [? [? ?]]; auto.
 destruct (list_norepet_append_inv _ _ _ H) as [? [? ?]]; auto.
 rewrite H3.
 exists (Vptr b Int.zero), (b,0).
 split.
 split.
 unfold type_of_global.
 case_eq (Genv.find_var_info (Genv.globalenv prog) b); intros.
 apply Genv.find_var_info_positive in H5.
 apply Genv.find_funct_ptr_negative in H4. omegaContradiction.
 rewrite H4.
 repeat f_equal.
 unfold no_dups in H.
 apply list_norepet_append_left in H.
 forget (prog_funct prog) as g.
 clear - H H0 H1 H2.
 unfold match_fdecs in H0. 
 revert G H H0 H1 H2; induction g; simpl; intros. 
 contradiction.
 inv H. destruct G; inv H0.
 simpl in H1. destruct p as [i p]. destruct a as [i' a].
 simpl in H3; subst i'. simpl in *.
 destruct H1. inv H. destruct H2. inv H; auto.
 apply in_map_fst in H. contradiction.
 destruct H2. inv H0.
 contradiction H5.
 clear - H H7. apply in_map_fst in H.
 revert G H H7; induction g; destruct G; simpl; intros; try contradiction; auto.
 inv H7. destruct a; destruct p; simpl in *; inv H7. destruct H; auto; right.
 apply (IHg G); auto.
 eapply IHg; eauto.
 simpl. rewrite Int.signed_zero; auto.
 unfold func_at. destruct fs.
 unfold initial_core.
 hnf. rewrite resource_at_make_rmap.
 rewrite level_make_rmap.
 unfold initial_core'.
 simpl.
 rewrite (Genv.find_invert_symbol (Genv.globalenv prog) id); auto.
 rewrite (find_id_i _ _ _ H1); auto.
 apply list_norepet_append_inv in H. destruct H as [H _].
 clear - H0 H.
 forget (prog_funct prog) as fs.
 unfold match_fdecs in H0.
 revert G H H0; induction fs; destruct G; intros. constructor. inv H0.
 constructor. inv H. simpl in H0. inv H0.
 simpl. rewrite <- H1. constructor.
 rewrite (fst_match_fdecs H5) in H3; auto.
 rewrite (fst_match_fdecs H5) in H4; auto.
 intros loc'  [fsig' A' P' Q'].
 unfold func_at.
 intros w ? ?.
 hnf in H2.
 assert (exists pp, initial_core (Genv.globalenv prog) G n @ loc' = PURE (FUN fsig') pp).
case_eq (initial_core (Genv.globalenv prog) G n @ loc'); intros.
destruct (necR_NO _ _ loc' t H1) as [? _].
rewrite H4 in H2 by auto.
inv H2.
eapply necR_YES in H1; try apply H3.
rewrite H1 in H2; inv H2.
eapply necR_PURE in H1; try apply H3.
rewrite H1 in H2; inv H2; eauto.
destruct H3 as [pp ?].
unfold initial_core in H3.
rewrite resource_at_make_rmap in H3.
unfold initial_core' in H3.
if_tac in H3; [ | inv H3].
simpl.
revert H3; case_eq (Genv.invert_symbol (Genv.globalenv prog) (fst loc')); intros;
  [ | congruence].
revert H5; case_eq (find_id i G); intros; [| congruence].
destruct f; inv H6.
apply Genv.invert_find_symbol in H3.
exists i.
simpl ge_of. unfold filter_genv. rewrite H3.
 destruct loc' as [b' z']; simpl in *; subst.
 exists (Vptr b' Int.zero).
 split.
  split.
 unfold type_of_global.
unfold type_of_funspec. simpl.
 assert (exists f, In (i,f) (prog_funct prog) /\ type_of_fundef f = Tfunction (type_of_params (fst fsig')) (snd fsig')).
 clear - H0 H5.
 forget (prog_funct prog) as g. unfold match_fdecs in H0.
 revert G H0 H5; induction g; destruct G; simpl; intros. inv H5. inv H0. inv H0.
 destruct p1. destruct a. simpl in *. inv H0.
 if_tac in H5. subst i0. inv H5. exists f0; split; auto.
 destruct (IHg G) as [f3 [? ?]]; auto. exists f3; split; auto.
 destruct H4 as [f [H4 H4']].
 destruct (Genv.find_funct_ptr_exists prog i f) as [b [? ?]]; auto.
 apply list_norepet_append_inv in H; intuition.
 apply list_norepet_append_inv in H; intuition.
 inversion2 H3 H6.
 case_eq (Genv.find_var_info (Genv.globalenv prog) b'); intros.
 apply Genv.find_var_info_positive in H6.
 apply Genv.find_funct_ptr_negative in H7. omegaContradiction.
 rewrite H7.
 repeat f_equal.
 auto.
 simpl. rewrite Int.signed_zero.
 auto.
 apply find_id_e in H5. apply in_map_fst in H5. auto.
Qed.

Definition initial_jm (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: no_dups (prog_funct prog) (prog_vars prog))
        (H2: match_fdecs (prog_funct prog) G) : juicy_mem :=
  initial_mem m (initial_core (Genv.globalenv prog) G n)
           (initial_core_ok _ _ _ H1 H2).

Lemma prog_contains_prog_funct: forall prog: program,  
        no_dups (prog_funct prog) (prog_vars prog) ->
          prog_contains (Genv.globalenv prog) prog.(prog_funct).
Proof.
  intros; intro; intros.
  assert (In id
     (map (fst (A:=ident) (B:=fundef)) (prog_funct prog) ++
      map (var_name _) (prog_vars prog))).
  apply in_or_app. left.
  replace id with (fst (id,f)) by (simpl; auto).
  apply in_map; auto.
  destruct (list_norepet_append_inv _ _ _ H) as [? [? ?]].
  apply (Genv.find_funct_ptr_exists prog id f); auto.
Qed.

(* there's a place this lemma should be applied, perhaps in seplog_soundness
    proof of semax_call *)
Lemma funassert_rho:
  forall G rho rho', ge_of rho = ge_of rho' -> funassert G rho |-- funassert G rho'.
Proof.
unfold funassert; intros.
rewrite H; auto.
Qed.

Lemma core_inflate_initial_mem:
  forall (m: mem) (prog: program) (G: funspecs) (n: nat), 
    match_fdecs (prog_funct prog) G ->
    no_dups (prog_funct prog) (prog_vars prog) ->
   core (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)) =
         initial_core (Genv.globalenv prog) G n.
Proof.
intros.
unfold inflate_initial_mem, initial_core; simpl.
apply rmap_ext.
rewrite level_core. do 2 rewrite level_make_rmap; auto.
intro.
rewrite <- core_resource_at.
repeat rewrite resource_at_make_rmap.
unfold inflate_initial_mem'.
rewrite <- core_resource_at.
repeat rewrite resource_at_make_rmap.
unfold initial_core'.
case_eq (Genv.invert_symbol (Genv.globalenv prog) (fst l)); intros; auto.
rename i into id.
case_eq (find_id id G); intros; auto.
rename f into fs.
assert (exists f, In (id,f) (prog_funct prog)).
apply find_id_e in H2. apply in_map_fst in H2; rewrite <- (fst_match_fdecs H) in H2.
forget (prog_funct prog) as g; clear - H2.
induction g; simpl in *. contradiction. destruct a; destruct H2; simpl in *; eauto.
destruct (IHg H); eauto.
destruct H3 as [f ?].
apply Genv.invert_find_symbol in H1.
destruct (list_norepet_append_inv _ _ _ H0) as [? [? ?]]; auto.
destruct (Genv.find_funct_ptr_exists prog id f) as [b [? ?]]; auto.
inversion2 H1 H7.
assert (fst l < 0) by (eapply Genv.find_funct_ptr_negative; eauto).
unfold access_at.
rewrite nextblock_noaccess by omega.
if_tac; auto.
destruct fs; repeat rewrite core_PURE; auto.
repeat rewrite core_NO; auto.
if_tac; rewrite core_NO;
destruct (access_at m l); intros; try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
if_tac; rewrite core_NO;
destruct (access_at m l); intros; try destruct p; try rewrite core_YES; try rewrite core_NO; auto.
Qed.

Lemma writable_blocks_app:
 forall rho l1 l2, writable_blocks (l1++l2) rho = writable_blocks l1 rho * writable_blocks l2 rho. Proof.
induction l1; intros; simpl.
rewrite emp_sepcon; auto.
destruct a.
rewrite IHl1.
rewrite sepcon_assoc; auto.
Qed.

Lemma writable_blocks_rev:
  forall rho l, writable_blocks l rho = writable_blocks (rev l) rho.
Proof.
induction l; simpl; auto.
destruct a.
rewrite writable_blocks_app.
rewrite <- IHl.
simpl.
rewrite sepcon_emp.
apply sepcon_comm.
Qed.


Lemma add_variables_nextblock:
  forall F V vl (ge: Genv.t F V) i g ul, list_norepet (map (var_name V) (vl++(i,g)::ul)) ->
   Genv.find_symbol (Genv.add_variables ge (vl++(i,g)::ul)) i = 
          Some (Genv.genv_nextvar ge + Z_of_nat (length vl)).
Proof.
 induction vl; intros.
 simpl.
 rewrite Genv.add_variables_same_symb.
 unfold Genv.find_symbol, Genv.add_variable.
 simpl. rewrite PTree.gss. f_equal; unfold block; omega.
 simpl in H. inv H. apply H2.
 simpl length. rewrite inj_S. 
 transitivity (Some (Genv.genv_nextvar (Genv.add_variable ge a) + (Z_of_nat (length vl)))).
 rewrite <-  (IHvl (Genv.add_variable ge a) i g ul).
 f_equal.
 inv H; auto.
 f_equal.
 forget (Z_of_nat (length vl)) as n.
 simpl. omega.
Qed.

Lemma initial_writable_blocks:
  forall prog G m n,
     no_dups (prog_funct prog) (prog_vars prog) ->
    match_fdecs (prog_funct prog) G ->
    Genv.init_mem prog = Some m ->
     app_pred 
      (writable_blocks (map (initblocksize type) (prog_vars prog))
          (empty_environ (Genv.globalenv prog)))
  (inflate_initial_mem m (initial_core (Genv.globalenv prog) G n)).
Proof.
 intros until n. intros ? SAME_IDS ?.
 assert (IOK: initial_rmap_ok  (initial_core (Genv.globalenv prog) G n))
    by (apply initial_core_ok; auto).
  unfold Genv.init_mem in H0.
  unfold Genv.globalenv in *.
  destruct prog as [fl main vl].
  simpl in *.
  assert (H9: Genv.genv_nextvar (Genv.add_functions (Genv.empty_genv fundef type) fl) = 1).
  clear. rewrite Genv.add_functions_nextvar. reflexivity.
  forget (Genv.add_functions (Genv.empty_genv fundef type) fl) as ge.
  destruct (list_norepet_append_inv _ _ _ H) as [_ [H' _]].
  clear H; rename H' into H.
  clear - H H0 IOK H9.
  remember (Genv.add_variables ge vl) as gev.
  rewrite <- (rev_involutive vl) in *.
  rewrite alloc_variables_rev_eq in H0.
  forget (rev vl) as vl'. clear vl; rename vl' into vl.
  rewrite map_rev. rewrite <- writable_blocks_rev.
  assert (exists ul, gev = Genv.add_variables ge (rev vl ++ ul) /\ 
                                       list_norepet (map (var_name type) (rev vl ++ ul))).
  exists nil; rewrite <- app_nil_end; auto.
  clear Heqgev H.
  revert m H0 H1; induction vl; simpl; intros.
 apply resource_at_empty2.
 intro l.
 unfold inflate_initial_mem.
 rewrite resource_at_make_rmap.
 unfold inflate_initial_mem'.
  inv H0.
 unfold access_at, empty. simpl. rewrite ZMap.gi.
 rewrite <- core_resource_at. apply core_identity.
 invSome.
 case_eq (initblocksize type a); intros.
 specialize (IHvl _ H0).
 unfold writable_block.
 normalize.
 unfold initblocksize in H.
 destruct a. inv H.
 unfold Genv.alloc_variable in H3.
 simpl in H3.
 revert H3; case_eq (alloc m0 0 (Genv.init_data_list_size (gvar_init g))); intros.
 invSome. invSome.
 unfold empty_environ at 1. simpl ge_of. unfold filter_genv.
 destruct H1 as [ul [? ?]].
 spec IHvl.
  exists ((i,g)::ul).
 rewrite app_ass in H1,H2; split; auto.
 assert (Genv.find_symbol gev i = Some b).
 clear - H0 H H1 H2 H9.
 apply alloc_result in H. subst.
 rewrite <- alloc_variables_rev_eq in H0. 
 apply Genv.alloc_variables_nextblock in H0.
 rewrite H0. clear - H2 H9.
 rewrite app_ass in *. simpl app in *.
 simpl nextblock. rewrite <- H9.
 apply add_variables_nextblock; auto. 
 rewrite H4.
 exists (Vptr b Int.zero, match type_of_global gev b with
      | Some t => t
      | None => Tvoid
      end).
 normalize.
 exists (b, 0).
 normalize; exists Share.bot.
 normalize.
 split.
 simpl. split.
 destruct (type_of_global gev b); auto.
 f_equal; rewrite Int.signed_zero; auto.
 rewrite sepcon_comm.
 assert (b>0). apply alloc_result in H. subst; apply nextblock_pos.
 apply (mem_alloc_juicy _ _ _ _ _ H
                    (initial_core gev G n)
                   (writable_blocks (map (initblocksize type) vl) (empty_environ gev))
                  IOK IOK) in IHvl.
 rewrite Zminus_0_r in IHvl.
 apply (store_zeros_lem _ _ _ _ H3 H7 _ IOK IOK) in IHvl.
 apply (store_init_data_list_lem _ _ _ _ _ _ _ _ H5 H7 _ IOK IOK) in IHvl.
 rewrite <- (Zminus_0_r  (Genv.init_data_list_size (gvar_init g))) in IHvl.
 assert (Genv.perm_globvar g = Writable) by admit. (* need to generalize this! *)
 rewrite H8 in *.
 apply (drop_perm_writable_lem _ _ _ _ _ H6 H7 _ IOK IOK) in IHvl.
 rewrite Zminus_0_r in IHvl.
 apply IHvl.
Qed.

Lemma semax_prog_rule :
  forall z G prog m,
     semax_prog prog G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, 
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       make_initial_core (juicy_core_sem cl_core_sem)
                    (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
       forall n, exists jm, 
       m_dry jm = m /\ level jm = n /\ 
       jsafeN Hspec (Genv.globalenv prog) n z q jm.
Proof.
 intros until m.
 pose proof I; intros.
 destruct H0 as [? [[? ?] ?]].
 assert (exists f, In (prog_main prog, f) (prog_funct prog) ).
 clear - H4 H2.
 forget (prog_main prog) as id.
 apply in_map_fst in H4. rewrite <- (fst_match_fdecs H2) in H4.
 forget (prog_funct prog) as g.
 clear - H4; induction g. inv H4. destruct H4.
 destruct a; simpl; eauto.
 destruct (IHg H).
 exists x; right; auto.
 destruct H5 as [f ?].
 apply compute_list_norepet_e in H0.
destruct (Genv.find_funct_ptr_exists prog (prog_main prog) f) as [b [? ?]]; auto.
 destruct (list_norepet_append_inv _ _ _ H0) as [? [? ?]]; auto.
 destruct (list_norepet_append_inv _ _ _ H0) as [? [? ?]]; auto.
 exists b.
 unfold make_initial_core; simpl.
econstructor.
 split3; auto.
 reflexivity.
 intro n.
 exists (initial_jm _ _ _ n H1 H0 H2).
 split3.
 simpl. auto.
 simpl.
 rewrite inflate_initial_mem_level.
 unfold initial_core. rewrite level_make_rmap; auto.
 specialize (H3 (Genv.globalenv prog) (prog_contains_prog_funct _ H0)).
 unfold temp_bindings. simpl length. simpl typed_params. simpl type_of_params.
pattern n at 1; replace n with (level (m_phi (initial_jm prog m G n H1 H0 H2))).
pose (rho := mkEnviron (filter_genv (Genv.globalenv prog)) empty_env 
                      (PTree.set 1 (Vptr b Int.zero) (PTree.empty val))).
change empty_env  with (ve_of rho).
change (PTree.set 1 (Vptr b Int.zero) (PTree.empty val)) with (te_of rho).
eapply semax_call_aux with (Delta :=Delta1)(F0:= fun _ => TT)
         (R := normal_ret_assert (fun _ => TT)) (F:=TT)
          (x := tt)(Q := fun _ => main_post prog tt);
  try apply H3; try eassumption.
admit.  (* typechecking proof *)
reflexivity.
admit.  (* typechecking proof *)
hnf; intros; intuition.
hnf; intros; intuition.
unfold normal_ret_assert; simpl.
simpl.
extensionality rho'.
unfold main_post.
normalize. rewrite TT_sepcon_TT. auto.
reflexivity.
unfold expr.eval_expr; simpl; reflexivity.
rewrite (corable_funassert G rho).
simpl m_phi.
rewrite core_inflate_initial_mem; auto.
destruct (list_norepet_append_inv _ _ _ H0) as [? [? ?]]; auto.
unfold rho; apply funassert_initial_core; auto.
intros ek vl rho'.
unfold normal_ret_assert.
normalize.
rewrite TT_sepcon_TT.
normalize.
apply derives_subp.
normalize.
simpl.
intros ? ? ? ? ?.
destruct H9 as [[? ?] ?].
hnf in H9, H11. subst ek vl.
destruct H8.
subst a.
change Clight_new.true_expr with true_expr.
change (level (m_phi jm)) with (level jm).
apply safe_loop_skip.
intros.
intros ? ?.
split; apply derives_imp; auto.
unfold main_pre.
apply now_later.
rewrite TT_sepcon_TT.
rewrite sepcon_comm.
apply sepcon_TT.
simpl.
apply initial_writable_blocks; auto.
simpl.
rewrite inflate_initial_mem_level.
unfold initial_core.
apply level_make_rmap.
Qed.

End semax_prog.

