Require Import VST.progs64.io_specs.
Require Import VST.progs64.io.
Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.initial_world.
Require Import VST.veric.SequentialClight.
Require Import VST.progs64.dry_mem_lemmas.

Section IO_Dry.

Context {E : Type -> Type} {IO_E : @IO_event nat -< E} `{!VSTGS (@IO_itree E) Σ}.

Definition getchar_pre (m : mem) (witness : byte -> IO_itree) (z : IO_itree) :=
  let k := witness in (sutt eq (r <- read stdin;; k r) z).

Definition getchar_post (m0 m : mem) (r : int) (witness : byte -> IO_itree) (z : IO_itree) :=
  m0 = m /\ -1 <= Int.signed r <= Byte.max_unsigned /\
  let k := witness in if eq_dec (Int.signed r) (-1) then sutt eq (r <- read stdin;; k r) z else z = k (Byte.repr (Int.signed r)).

Definition putchar_pre (m : mem) (witness : byte * IO_itree) (z : IO_itree) :=
  let '(c, k) := witness in (sutt eq (write stdout c;; k) z).

Definition putchar_post (m0 m : mem) (r : int) (witness : byte * IO_itree) (z : IO_itree) :=
  m0 = m /\ let '(c, k) := witness in
  (Int.signed r = -1 \/ Int.signed r = Byte.unsigned c) /\
  if eq_dec (Int.signed r) (-1) then sutt eq (write stdout c;; k) z else z = k.

Context (ext_link : String.string -> ident).

Definition getchar_sig := typesig2signature ([], tint) cc_default.

(*(* up *)
Lemma add_funspecs_pre
              {fs id sig cc E0 A P Q}
              Espec tys ge_s {x} {args} m z :
  let ef := EF_external id (typesig2signature sig cc) in
  funspecs_norepeat fs ->
  In (ext_link id, (mk_funspec sig cc E0 A P Q)) fs -> ∃ H : ext_spec_type (add_funspecs_rec _ ext_link Espec fs) ef = (nat * iResUR Σ * dtfr A)%type,
  ext_spec_pre (add_funspecs_rec _ ext_link Espec fs) ef x ge_s tys args z m <->
  funspec2pre' _ A P (eq_rect _ Datatypes.id x _ H) ge_s (sig_args (ef_sig ef)) args z m.
Proof.
  induction fs; [intros; exfalso; auto|]; intros ?? [-> | H1]; simpl in *.
  - clear IHfs H; unfold funspec2jspec; simpl.
    destruct sig; unfold funspec2pre, funspec2post; simpl in *.
    revert x; if_tac; simpl; last done.
    intros; exists eq_refl; tauto.
  - assert (Hin: In (ext_link id) (map fst fs)).
    { eapply (in_map fst) in H1; apply H1. }
    inversion H as [|? ? Ha Hb]; subst.
    destruct a; simpl; destruct f as [(?, ?)]; simpl; unfold funspec2pre, funspec2post; simpl.
    revert x; simpl; if_tac [e | e].
    { injection e as ?; subst i; destruct fs; [solve [simpl; intros; exfalso; auto]|]; done. }
    intros; apply IHfs; auto.
Qed.*)

Lemma getchar_pre_plain : forall p w z m,
  ext_spec_pre (IO_ext_spec ext_link) (EF_external "getchar" getchar_sig) w p [] [] z m ->
    exists H : ext_spec_type (IO_ext_spec ext_link) (EF_external "getchar" getchar_sig) = (nat * iResUR Σ * (byte -> IO_itree))%type,
    getchar_pre m (snd (eq_rect _ Datatypes.id w _ H)) z.
Proof.
  intros.
  edestruct @add_funspecs_pre as (Hty & Hpre).
  { instantiate (1 := IO_specs ext_link).
    repeat constructor; simpl; try tauto. admit. }
  { simpl. right; left; unfold getchar_spec.
         instantiate (3 := ConstType (byte -> IO_itree)).
         reflexivity. }
  exists Hty; rewrite Hpre /funspec2pre' /= in H.
  if_tac in H.
    rewrite Hpre /=.
    2: { 
         f_equal. f_equal.
rewrite /= /funspec2pre.
    revert H.
    destruct (oi_eq_dec _ _).
  split.


Program Definition io_dry_spec : external_specification mem external_function (@IO_itree E).
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type io_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|exact False]];
      match goal with T := (_ * ?A)%type |- _ => exact (mem * A)%type end.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      exact (X1 = [Vubyte (fst w)] /\ m0 = X3 /\ putchar_pre X3 w X2).
    + destruct X as (m0 & _ & w).
      exact (X1 = [] /\ m0 = X3 /\ getchar_pre X3 w X2).
  - simpl; intros ??? ot ???.
    destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|contradiction]].
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (ot <> AST.Tvoid /\ putchar_post m0 X3 i w X2).
    + destruct X as (m0 & _ & w).
      destruct X1; [|exact False].
      destruct v; [exact False | | exact False | exact False | exact False | exact False].
      exact (ot <> AST.Tvoid /\ getchar_post m0 X3 i w X2).
  - intros; exact True.
Defined.

Definition dessicate : forall ef (jm : juicy_mem), ext_spec_type io_ext_spec ef -> ext_spec_type io_dry_spec ef.
Proof.
  simpl; intros.
  destruct (oi_eq_dec _ _); [|destruct (oi_eq_dec _ _); [|assumption]].
  - destruct X as [_ X]; exact (m_dry jm, X).
  - destruct X as [_ X]; exact (m_dry jm, X).
Defined.

Theorem juicy_dry_specs : juicy_dry_ext_spec _ io_ext_spec io_dry_spec dessicate.
Proof.
  split; [|split]; try reflexivity; simpl.
  - unfold funspec2pre, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct t as (? & ? & (c, k)); simpl in *.
      destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      destruct e; inv H; simpl in *.
      destruct vl; try contradiction; simpl in *.
      destruct H0, vl; try contradiction.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      assert (Harg: v = Vubyte c) by (inv Hargs; auto). clear Hargs.
      rewrite Harg.
      eapply has_ext_compat in Hext as []; eauto; subst; auto.
      eexists; eauto.
    + unfold funspec2pre; simpl.
      if_tac; [|contradiction].
      intros; subst.
      destruct t as (? & ? & k); simpl in *.
      destruct H2 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
      destruct e; inv H0; simpl in *.
      destruct vl; try contradiction.
      unfold putchar_pre; split; auto; split; auto.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      eapply has_ext_compat in Hext as []; eauto; subst; auto.
      eexists; eauto.
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac.
    + intros; subst.
      destruct H0 as (_ & vl & z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & (c, k)); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      edestruct (has_ext_compat _ z0 _ (m_phi jm0) Htrace) as (? & ? & ?); eauto; [eexists; eauto|]; subst.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (? & Hmem & ? & Hw); simpl in Hw; subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 (Some (ext_ghost x, NoneP) :: tl (ghost_of phi0)) _)), (age_to.age_to (level jm) phi1'); auto.
      { rewrite <- ghost_of_approx at 2; simpl.
        destruct (ghost_of phi0); auto. }
      split; [|split].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists i.
        split3; simpl.
        -- split; auto.
        -- unfold_lift. split; auto. split; [|intro Hx; inv Hx].
             unfold eval_id; simpl. unfold semax.make_ext_rval; simpl.
             destruct ot; try contradiction; reflexivity.
        -- unfold SEPx; simpl.
           rewrite seplog.sepcon_emp.
           unfold ITREE; exists x; split; [if_tac; auto|].
           { subst; apply eutt_sutt, Reflexive_eqit_eq. }
           eapply age_to.age_to_pred, change_has_ext; eauto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
    + unfold funspec2pre, funspec2post, dessicate; simpl.
      if_tac; [|contradiction].
      clear H0.
      intros; subst.
      destruct H0 as (_ & vl & z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
      destruct t as (phi1 & t); subst; simpl in *.
      destruct t as (? & k); simpl in *.
      unfold SEPx in Hpre; simpl in Hpre.
      rewrite seplog.sepcon_emp in Hpre.
      destruct Hpre as [_ [Hargs [_ [it [H8 Htrace]]]]].
      edestruct (has_ext_compat _ z0 _ (m_phi jm0) Htrace) as (? & ? & ?); eauto; [eexists; eauto|]; subst.
      destruct v; try contradiction.
      destruct v; try contradiction.
      destruct H4 as (? & Hmem & ? & Hw); simpl in Hw; subst.
      rewrite <- Hmem in *.
      rewrite rebuild_same in H2.
      unshelve eexists (age_to.age_to (level jm) (set_ghost phi0 (Some (ext_ghost x, NoneP) :: tl (ghost_of phi0)) _)), (age_to.age_to (level jm) phi1'); auto.
      { rewrite <- ghost_of_approx at 2; simpl.
        destruct (ghost_of phi0); auto. }
      split; [|split].
      * eapply age_rejoin; eauto.
        intro; rewrite H2; auto.
      * exists i.
        split3; simpl.
        -- split; auto.
        -- unfold_lift. split; auto. split; [|intro Hx; inv Hx].
             unfold eval_id; simpl. unfold semax.make_ext_rval; simpl.
             destruct ot; try contradiction; reflexivity.
        -- unfold SEPx; simpl.
             rewrite seplog.sepcon_emp.
             unfold ITREE; exists x; split; [if_tac; auto|].
             { subst; apply eutt_sutt, Reflexive_eqit_eq. }
             eapply age_to.age_to_pred, change_has_ext; eauto.
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
Qed.

Instance mem_evolve_refl : Reflexive mem_evolve.
Proof.
  repeat intro.
  destruct (access_at x loc Cur); auto.
  destruct p; auto.
Qed.

Lemma dry_spec_mem : ext_spec_mem_evolve _ io_dry_spec.
Proof.
  intros ??????????? Hpre Hpost.
  simpl in Hpre, Hpost.
  simpl in *.
  if_tac in Hpre.
  - destruct w as (m0 & _ & w).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost as (? & ? & ?); subst.
    reflexivity.
  - if_tac in Hpre; [|contradiction].
    destruct w as (m0 & _ & w).
    destruct Hpre as (_ & ? & Hpre); subst.
    destruct v; try contradiction.
    destruct v; try contradiction.
    destruct Hpost as (? & ? & ?); subst.
    reflexivity.
Qed.

End IO_Dry.
