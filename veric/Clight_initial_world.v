Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.

Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.

Require Export VST.veric.initial_world.

Local Open Scope pred.

Obligation Tactic := idtac.

(*
Definition initial_core' (ge: Genv.t fundef type) (G: funspecs) (n: nat) (loc: address) : resource :=
   if Z.eq_dec (snd loc) 0
   then match Genv.invert_symbol ge (fst loc) with
           | Some id =>
                  match find_id id G with
                  | Some (mk_funspec fsig cc A P Q _ _) =>
                           PURE (FUN fsig cc) (SomeP (SpecTT A) (fun ts => fmap _ (approx n) (approx n) (packPQ P Q ts)))
                  | None => NO Share.bot bot_unreadable
                  end
           | None => NO Share.bot bot_unreadable
          end
   else NO Share.bot bot_unreadable.*)
Notation initial_core' := (initial_core' function).

(* This version starts with an empty ghost. 
Program Definition initial_core (ge: Genv.t fundef type) (G: funspecs) (n: nat): rmap :=
  proj1_sig (make_rmap (initial_core' ge G n) nil n _ eq_refl).
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
f_equal.
change R.approx with approx.
extensionality i0 ts b rho.
rewrite fmap_app.
pattern (approx n) at 7 8 9.
rewrite <- approx_oo_approx.
auto.
Qed.*)
Notation initial_core := (@initial_core function).

(*
Program Definition initial_core_ext {Z} (ora : Z) (ge: Genv.t fundef type) (G: funspecs) (n: nat): rmap :=
  proj1_sig (make_rmap (initial_core' ge G n) (Some (ext_ghost ora, NoneP) :: nil) n _ eq_refl).
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
f_equal.
change R.approx with approx.
extensionality i0 ts b rho.
rewrite fmap_app.
pattern (approx n) at 7 8 9.
rewrite <- approx_oo_approx.
auto.
Qed.
*)
Notation initial_core_ext := (@initial_core_ext  function).

(*Definition prog_funct (p: program) := prog_funct' (prog_defs p).*)
Notation prog_funct := (@prog_funct function).

Inductive match_fdecs: list  (ident * fundef) -> funspecs -> Prop :=
| match_fdecs_nil: match_fdecs nil nil
| match_fdecs_cons: forall i fd fspec fs G,
                  type_of_fundef fd = type_of_funspec fspec ->
                  match_fdecs fs G ->
                  match_fdecs ((i,fd)::fs) ((i,fspec)::G)
(* EXPERIMENT
| match_fdecs_skip: forall ifd fs G,
                 match_fdecs fs G ->
                 match_fdecs (ifd::fs) G*)
.
(*
Fixpoint match_fdecs (fdecs: list (ident * fundef)) (G: funspecs) :=
 match fdecs, G with
 | _, nil => True
 | (i,fd)::f', (j,fspec)::G' =>
       i=j /\ type_of_fundef fd = type_of_funspec fspec /\ match_fdecs f' G'
        \/ match_fdecs f' G
 | nil, _::_ => False
 end.
*)
(*
Definition match_fdecs (fdecs: list (ident * fundef)) (G: funspecs) :=
 map (fun idf => (fst idf, Clight.type_of_fundef (snd idf))) fdecs =
 map (fun idf => (fst idf, type_of_funspec (snd idf))) G.
*)


Lemma match_fdecs_exists_Gfun:
  forall prog G i f,
    find_id i G = Some f ->
    match_fdecs (prog_funct prog) G ->
    exists fd,   In (i, Gfun fd) (prog_defs prog) /\
                     type_of_fundef fd = type_of_funspec f.
Proof. unfold prog_funct. unfold prog_defs_names.
intros ? ? ? ?.
forget (prog_defs prog) as dl.
revert G; induction dl; simpl; intros.
inv H0. inv H.
destruct a as [i' [?|?]].
inv H0.
simpl in H; if_tac in H. subst i'; inv H.
eauto.
destruct (IHdl G0) as [fd [? ?]]; auto.
exists fd; split; auto.
destruct (IHdl G) as [fd [? ?]]; auto.
exists fd; split; auto.
(* EXPERIMENT
destruct (IHdl G) as [fd [? ?]]; auto.
exists fd; split; auto.
*)
Qed.

(*Specializations of stuff in initial_world:
(*Partial attempt at porting add_globales_hack*)
Lemma add_globals_hack_nil:
   forall gev prog_pub,
    gev = Genv.add_globals (Genv.empty_genv fundef type prog_pub) (rev nil) ->
   forall id, Genv.find_symbol gev id = None.
Proof. simpl; intros; subst.
  unfold Genv.find_symbol, Genv.empty_genv. simpl. apply PTree.gempty.
Qed.

Lemma add_globals_hack_single:
   forall v gev prog_pub,
    gev = Genv.add_globals (Genv.empty_genv fundef type prog_pub) (cons v nil) ->
   forall id b, (Genv.find_symbol gev id = Some b <-> fst v = id /\ b = 1%positive).
Proof. simpl; intros; subst.
  unfold Genv.find_symbol, Genv.empty_genv. simpl.
  destruct (peq (fst v) id).
     subst id. rewrite PTree.gss.
       split; intros. split; trivial. congruence.
       destruct H; subst. trivial.
  rewrite PTree.gso.
    split; intros. rewrite PTree.gempty in H. inv H.
    destruct H; subst. congruence.
  auto.
Qed.

Lemma add_globals_hack:
   forall vl gev prog_pub,
    list_norepet (map fst vl) ->
    gev = Genv.add_globals (Genv.empty_genv fundef type prog_pub) (rev vl) ->

   (forall id b, 0 <= Zpos b - 1 < Zlength vl ->
                           (Genv.find_symbol gev id = Some b <->
                            nth_error (map (@fst _ _) vl) (length vl - Pos.to_nat b)  = Some id)).
Proof. intros. subst.
     apply iff_trans with (nth_error (map fst (rev vl)) (nat_of_Z (Zpos b - 1)) = Some id).
   2: {
     rewrite map_rev; rewrite nth_error_rev.
             replace (length (map fst vl) - nat_of_Z (Zpos b - 1) - 1)%nat
                        with (length vl - Pos.to_nat b)%nat ; [intuition | ].
    rewrite map_length.
    transitivity (length vl - (nat_of_Z (Z.pos b-1)+1))%nat; try omega.
    f_equal.
    change (Pos.to_nat b = (nat_of_Z (Z.pos b - 1) + nat_of_Z 1)%nat).
    rewrite <- nat_of_Z_plus by omega.
    rewrite <- Z2Nat.inj_pos. unfold nat_of_Z.
    f_equal. omega.
    rewrite map_length.
    rewrite Zlength_correct in H1.
    forget (Z.pos b-1) as i; forget (length vl) as n; clear - H1.
    apply inj_lt_rev. rewrite nat_of_Z_max; auto.
    rewrite (Coqlib.Zmax_spec i 0). if_tac; omega.
  }
  rename H1 into Hb; revert H; induction vl; simpl rev; simpl map;
       simpl Genv.find_symbol; intros;
       try rewrite Zlength_nil in *.
      unfold Genv.find_symbol. rewrite PTree.gempty.
     intuition.
       destruct a. inv H. rewrite Zlength_cons in Hb.
       destruct (eq_dec (Z.pos b-1) (Zlength vl)).
        clear IHvl Hb. rewrite e. rewrite Zlength_correct. rewrite nat_of_Z_of_nat.
        replace b with (Z.to_pos (1+ (Zlength vl)))
          by (rewrite <- e; replace (1 + (Z.pos b - 1)) with (Z.pos b) by omega;
                  apply Pos2Z.id).
        clear e b.
        rewrite <- Zlength_rev. rewrite <- rev_length.
         replace (length (rev vl)) with (length (rev vl) + 0)%nat by omega.
         rewrite map_app. rewrite <- map_length with (f:=@fst ident (globdef fundef type)).
        rewrite nth_error_app.
        apply iff_trans with (i=id); [ | simpl; split; intro; subst; auto; inv H; auto].
        rewrite In_rev in H2. rewrite <- map_rev in H2.
       rewrite <- list_norepet_rev in H3. rewrite <- map_rev in H3.
         forget (rev vl) as dl.
    assert (FSA := find_symbol_add_globals i g  id _ prog_pub H2 H3).
    { destruct dl.
      rewrite (FSA (Z.to_pos (1 + Zlength (@nil (ident * globdef fundef type))))).
      simpl. intuition.
      replace (Z.to_pos (1 + Zlength (p :: dl))) with (1 + Z.to_pos (Zlength (p :: dl)))%positive ; auto.
      clear.
      rewrite Zlength_cons.      rewrite Zlength_correct.
      rewrite Z2Pos.inj_add; try solve [simpl; omega]. reflexivity.
    }
    spec IHvl ; [ omega |].
    specialize (IHvl H3).
    rewrite Genv.add_globals_app.
    unfold Genv.add_globals at 1. simpl fold_left.
    unfold Genv.find_symbol, Genv.add_global.
    simpl Genv.genv_symb.
    destruct (eq_dec id i).
    + subst i. rewrite PTree.gss.
      rewrite Genv.genv_next_add_globals.
      rewrite advance_next_length.
      simpl Genv.genv_next.
      rewrite map_app.
      rewrite In_rev in H2. rewrite <- map_rev in H2. rewrite Pos.add_sub.
      split; intro.
      - assert (H': b = Pos.of_nat (S (length (rev vl)))) by congruence.
        clear H; rename H' into H.
          subst b. elimtype False; apply n; clear.
          rewrite <- Zlength_rev. rewrite Zlength_correct. forget (length (rev vl)) as i.
          rewrite Zpos_Posofnat by omega. rewrite Nat2Z.inj_succ. unfold Z.succ.  omega.
     - elimtype False.
       assert (Z.pos b-1 >= 0) by (clear - Hb; omega).
       pose proof (Coqlib.nat_of_Z_eq _ H0).
       clear - H1 H H2 n.
       rewrite Zlength_correct in n. apply n. clear n.
       rewrite <- H1.
       f_equal. clear - H H2.
       forget (nat_of_Z (Z.pos b-1)) as j.
       replace (length vl) with (length (map fst (rev vl)))
           by (rewrite map_length; rewrite rev_length; auto).
       forget (map fst (rev vl)) as al.
       revert al H2 H; clear; induction j; destruct al; simpl; intros; auto. inv H; intuition.
       elimtype False; clear - H; induction j; inv H; auto.
       f_equal. apply IHj; auto.
    + rewrite PTree.gso by auto.
      rewrite map_app.
      destruct IHvl.
      split; intro.
      - apply H in H1. rewrite nth_error_app1; auto.
        clear - n Hb. rewrite map_length. rewrite rev_length. rewrite Zlength_correct in Hb,n.
        assert (Z.pos b-1>=0) by omega.
        pose proof (Coqlib.nat_of_Z_eq _ H).
        forget (nat_of_Z(Z.pos b-1)) as j. rewrite <- H0 in *.
        destruct Hb. clear - H2 n. omega.
      - assert (nat_of_Z (Z.pos b-1) < length (map (@fst _ _) (rev vl)))%nat.
        { clear - Hb n H1.
          rewrite Zlength_correct in n. rewrite map_length; rewrite rev_length.
          assert (nat_of_Z (Z.pos b-1) <> length vl).
          { contradict n. rewrite <- n.
            rewrite Coqlib.nat_of_Z_eq; auto. omega. }
          forget (nat_of_Z (Z.pos b-1)) as j.
          clear - H1 H.
          assert (S (length vl) = length (map fst (rev vl) ++ map fst ((i, g) :: nil))).
          { simpl. rewrite app_length; rewrite map_length; rewrite rev_length; simpl; omega. }
          assert (j < S (length vl))%nat; [ | omega].
          rewrite H0. forget (map fst (rev vl) ++ map fst ((i, g) :: nil)) as al.
          clear - H1. revert al H1; induction j; destruct al; simpl in *; intros; inv H1; auto; try omega.
          specialize (IHj _ H0); omega. }
        rewrite nth_error_app1 in H1 by auto.
        apply H0 in H1. auto.
Qed.

Lemma find_symbol_globalenv:
  forall (prog: program) i b,
   list_norepet (prog_defs_names prog) ->
  Genv.find_symbol (Genv.globalenv prog) i = Some b ->
  0 < Z.pos b <= Z_of_nat (length (prog_defs prog)) /\
  exists d, nth_error (prog_defs prog) (nat_of_Z (Z.pos b-1)) = Some (i,d).
Proof.
intros.
unfold Genv.globalenv in H0.
change (AST.prog_public prog) with (prog_public prog) in H0.
change (AST.prog_defs prog) with (prog_defs prog) in H0.
assert (RANGE: 0 <= Z.pos b - 1 < Zlength (rev (prog_defs prog))). {
 rewrite <- (rev_involutive (prog_defs prog)) in H0.
 clear - H0.
 revert H0; induction (rev (prog_defs prog));  simpl Genv.find_symbol; intros.
 unfold Genv.find_symbol in H0. simpl in H0. rewrite PTree.gempty in H0; inv H0.
 rewrite Genv.add_globals_app in H0.
 simpl in H0. destruct a.
 destruct (eq_dec i0 i). subst.
 unfold Genv.add_global, Genv.find_symbol in H0. simpl in H0.
 rewrite PTree.gss  in H0. inv H0.
 clear.
 split.
 match goal with |- _ <= Z.pos ?A - _ => pose proof (Zgt_pos_0  A); omega end.
 rewrite Zlength_cons.
 induction l. simpl. omega.
 rewrite Zlength_cons.
 Opaque Z.sub. simpl. Transparent Z.sub.
 rewrite Genv.add_globals_app.
   simpl Genv.genv_next.
 match goal with |- context [Pos.succ ?J] =>
  forget J as j
 end.
 clear - IHl.
 replace (Z.pos (Pos.succ j) - 1) with (Z.succ (Z.pos j - 1)). omega.
  unfold Z.succ.  rewrite Pos2Z.inj_succ.  omega.
 unfold Genv.add_global, Genv.find_symbol in IHl, H0. simpl in H0.
 rewrite PTree.gso in H0 by auto.
 apply IHl in H0.
 rewrite Zlength_cons. omega.
 }
 split.
 rewrite Zlength_correct in RANGE.
 rewrite rev_length in RANGE. omega.
 rewrite <- list_norepet_rev in H.
 unfold prog_defs_names in H.
 change (AST.prog_defs prog) with (prog_defs prog) in H.
 rewrite <- map_rev in H.
 rewrite add_globals_hack in H0; [ | apply H | rewrite rev_involutive; auto | auto ].
 rewrite map_rev in H0.
 rewrite nth_error_rev in H0.
 rewrite list_map_nth in H0.
 match type of H0 with option_map _ ?A = _ =>
   revert H0; case_eq A; intros
 end.
 destruct p; simpl in H1. inv H1.
 exists g.
 rewrite <- H0. f_equal.
 rewrite rev_length. rewrite map_length.
 clear - RANGE.
 rewrite Zlength_rev in RANGE. rewrite Zlength_correct in RANGE.
 rewrite <- (Coqlib.nat_of_Z_eq (Z.pos b)) in * by omega.
 unfold nat_of_Z in *. rewrite Z2Nat.inj_pos in *.
 forget (Pos.to_nat b) as n. clear b.
 replace (Z.of_nat n - 1) with (Z.of_nat (n-1)) by (rewrite inj_minus1 by omega; f_equal; auto).
 rewrite Nat2Z.id.
 omega.
 inv H1.
 rewrite rev_length. rewrite map_length.
 clear - RANGE. rewrite Zlength_correct in RANGE.
 rewrite rev_length in RANGE.
 forget (length (prog_defs prog)) as N.
 assert (Z_of_nat N > 0) by omega.
 destruct N; inv H.
 assert (Pos.to_nat b > 0)%nat; [apply Pos2Nat.is_pos| omega].
Qed.*)

Lemma initial_core_ok: forall (prog: program) G n m,
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      Genv.init_mem prog = Some m ->
     initial_rmap_ok m (initial_core (Genv.globalenv prog) G n).
Proof.
intros.
rename H1 into Hm.
intros [b z]. simpl.
unfold initial_core; simpl.
rewrite <- core_resource_at.
rewrite resource_at_make_rmap.
unfold initial_core'.
simpl in *.
if_tac; [ | rewrite core_NO; auto].
case_eq (@Genv.invert_symbol (Ctypes.fundef function) type
       (@Genv.globalenv (Ctypes.fundef function) type prog) b);
   intros;  try now (rewrite core_NO; auto).
case_eq (find_id i G); intros; [ | rewrite core_NO; auto].
apply Genv.invert_find_symbol in H2.
pose proof (Genv.find_symbol_not_fresh _ _ Hm H2).
unfold valid_block in H4.
split; intros.
contradiction.
destruct (match_fdecs_exists_Gfun _ _ _ _ H3 H0) as [fd [? _]].
destruct f.
split; auto.
subst z.
destruct (find_symbol_globalenv _ _ _ H H2) as [RANGE [d ?]].
assert (d = Gfun fd).
clear - H H5 H1.
unfold prog_defs_names in H.
change (AST.prog_defs prog) with (prog_defs prog) in H.
forget (prog_defs prog) as dl. forget (nat_of_Z (Z.pos b-1)) as n.
revert dl H H5 H1; induction n; simpl; intros.
destruct dl; inv H1.
inv H. simpl in H5.
destruct H5. inv H; auto.
apply (in_map (@fst ident (globdef fundef type))) in H. simpl in H;  contradiction.
destruct dl; inv H1. inv H.
simpl in H5. destruct H5. subst.
clear - H2 H3. apply nth_error_in in H2.
apply (in_map (@fst ident (globdef fundef type))) in H2. simpl in *;  contradiction.
apply (IHn dl); auto.
(* end assert d = Gfun fd *)
subst d.
clear H5.
clear - RANGE H2 H1 H Hm.
unfold Genv.init_mem in Hm.
forget (Genv.globalenv prog) as ge.
change (AST.prog_defs prog) with (prog_defs prog) in Hm.
forget (prog_defs prog) as dl.
rewrite <- (rev_involutive dl) in H1,Hm.
rewrite nth_error_rev in H1.
2 : { rewrite rev_length. clear - RANGE.
      destruct RANGE.
      apply inj_lt_iff. rewrite Coqlib.nat_of_Z_eq by omega. omega. }
rename H1 into H5.
replace (length (rev dl) - nat_of_Z (Z.pos b - 1) - 1)%nat
 with (length (rev dl) - nat_of_Z (Z.pos b))%nat in H5.
2 : { rewrite rev_length.
      clear - RANGE.
      replace (nat_of_Z (Z.pos b-1)) with (nat_of_Z (Z.pos b) - 1)%nat.
      assert (nat_of_Z (Z.pos b) <= length dl)%nat.
      destruct RANGE.
      apply inj_le_iff. rewrite Coqlib.nat_of_Z_eq by omega. auto.
      assert (nat_of_Z (Z.pos b) > 0)%nat. apply inj_gt_iff.
      rewrite Coqlib.nat_of_Z_eq by omega.  simpl. omega.
      omega. destruct RANGE as [? _].
      apply nat_of_Z_lem1.
      assert (nat_of_Z (Z.pos b) > 0)%nat. apply inj_gt_iff. simpl.
      pose proof (Pos2Nat.is_pos b); omega.
      omega. }
assert (0 < nat_of_Z (Z.pos b) <= length dl)%nat.
{ clear - RANGE.
  destruct RANGE; split.
  apply inj_lt_iff. rewrite Coqlib.nat_of_Z_eq; try omega. simpl. auto.
  apply inj_le_iff. rewrite Coqlib.nat_of_Z_eq; try omega. }
clear RANGE; rename H0 into RANGE.
unfold nat_of_Z in *. rewrite Z2Nat.inj_pos in *.
rewrite <- rev_length in RANGE.
forget (rev dl) as dl'; clear dl; rename dl' into dl.
destruct RANGE.
rewrite alloc_globals_rev_eq in Hm.
revert m Hm H1 H5; induction dl; intros.
inv H5.
simpl in H1,Hm.
invSome.
specialize (IHdl _ Hm).
destruct (eq_dec (Pos.to_nat b) (S (length dl))).
+ rewrite e, minus_diag in H5. simpl in H5.
  inversion H5; clear H5; subst a.
  apply alloc_globals_rev_nextblock in Hm.
  rewrite Zlength_correct in Hm.
  rewrite <- inj_S in Hm. rewrite <- e in Hm.
  rewrite positive_nat_Z in Hm.  rewrite Pos2Z.id in Hm.
  subst b.
  clear IHdl H1 H0. clear dl e.
  unfold Genv.alloc_global in H6.
  revert H6; case_eq (alloc m0 0 1); intros.
  unfold drop_perm in H6.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable).
  unfold max_access_at, access_at; inv H6.
  simpl. apply alloc_result in H0. subst b.
  rewrite PMap.gss.
  simpl. auto.
  inv H6.
+ destruct IHdl.
  omega.
  replace (length (a::dl) - Pos.to_nat b)%nat with (S (length dl - Pos.to_nat b))%nat in H5.
  apply H5.
  simpl. destruct (Pos.to_nat b); omega.
  assert (b < nextblock m0)%positive.
  apply alloc_globals_rev_nextblock in Hm.
  rewrite Zlength_correct in Hm. clear - Hm n H1.
  rewrite Hm.
  apply Pos2Nat.inj_lt.
  pattern Pos.to_nat at 1; rewrite <- Z2Nat.inj_pos.
  rewrite Z2Pos.id by omega.
  rewrite Z2Nat.inj_succ by omega.
  rewrite Nat2Z.id. omega.
  destruct (alloc_global_old _ _ _ _ H6 (b,0)) as [? ?]; auto.
  unfold max_access_at.
  rewrite <- H8.
  split; auto.
Qed.

Definition initial_jm (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) : juicy_mem :=
  initial_mem m (initial_core (Genv.globalenv prog) G n)
           (initial_core_ok _ _ _ m H1 H2 H).

Lemma initial_jm_age (prog: program) m (G: funspecs) (n : nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) :
age
    (initial_mem m (initial_core (Genv.globalenv prog) G (S n)) (initial_core_ok _ _ _ m H1 H2 H))
    (initial_mem m (initial_core (Genv.globalenv prog) G    n ) (initial_core_ok _ _ _ m H1 H2 H)).
Proof.
apply age1_juicy_mem_unpack''; [ | reflexivity].
simpl.
unfold inflate_initial_mem in *.
match goal with |- context [ proj1_sig ?x ] => destruct x as (r & lev & bah & Hg1); simpl end.
match goal with |- context [ proj1_sig ?x ] => destruct x as (r' & lev' & bah' & Hg2); simpl end.
apply rmap_age_i.
rewrite lev,lev'.
unfold initial_core; simpl.
rewrite !level_make_rmap. auto.
intro loc.
rewrite bah, bah'.
unfold inflate_initial_mem'.
destruct (access_at m loc Cur); [ | reflexivity].
destruct p; unfold resource_fmap; f_equal; try apply preds_fmap_NoneP.
unfold initial_core.
rewrite !resource_at_make_rmap.
unfold initial_core'.
if_tac; auto.
unfold fundef.
destruct (Genv.invert_symbol (Genv.globalenv (program_of_program prog))
        (fst loc)); auto.
destruct (find_id i G); auto.
destruct f; auto.
f_equal.
simpl.
f_equal.
rewrite lev'.
unfold initial_core.
rewrite level_make_rmap.
extensionality ts x b rho.
rewrite fmap_app.
match goal with
| |- ?A (?B ?C) = _ => change (A (B C)) with ((A oo B) C)
end.
rewrite approx_oo_approx' by omega.
rewrite approx'_oo_approx by omega.
auto.
rewrite Hg1, Hg2.
unfold initial_core; rewrite !ghost_of_make_rmap; auto.
Qed.

Lemma initial_core_ext_ok: forall {Z} (ora : Z) (prog: program) G n m,
      list_norepet (prog_defs_names prog) ->
      match_fdecs (prog_funct prog) G ->
      Genv.init_mem prog = Some m ->
     initial_rmap_ok m (initial_core_ext ora (Genv.globalenv prog) G n).
Proof.
intros.
rename H1 into Hm.
intros [b z]. simpl.
unfold initial_core_ext; simpl.
rewrite <- core_resource_at.
rewrite resource_at_make_rmap.
unfold initial_core'.
simpl in *.
if_tac; [ | rewrite core_NO; auto].
case_eq (@Genv.invert_symbol (Ctypes.fundef function) type (@Genv.globalenv (Ctypes.fundef function) type prog) b);
   intros;  try now (rewrite core_NO; auto).
case_eq (find_id i G); intros; [ | rewrite core_NO; auto].
apply Genv.invert_find_symbol in H2.
pose proof (Genv.find_symbol_not_fresh _ _ Hm H2).
unfold valid_block in H4.
split; intros.
contradiction.
destruct (match_fdecs_exists_Gfun _ _ _ _ H3 H0) as [fd [? _]].
destruct f.
split; auto.
subst z.
destruct (find_symbol_globalenv _ _ _ H H2) as [RANGE [d ?]].
assert (d = Gfun fd).
clear - H H5 H1.
unfold prog_defs_names in H.
change (AST.prog_defs prog) with (prog_defs prog) in H.
forget (prog_defs prog) as dl. forget (nat_of_Z (Z.pos b-1)) as n.
revert dl H H5 H1; induction n; simpl; intros.
destruct dl; inv H1.
inv H. simpl in H5.
destruct H5. inv H; auto.
apply (in_map (@fst ident (globdef fundef type))) in H. simpl in H;  contradiction.
destruct dl; inv H1. inv H.
simpl in H5. destruct H5. subst.
clear - H2 H3. apply nth_error_in in H2.
apply (in_map (@fst ident (globdef fundef type))) in H2. simpl in *;  contradiction.
apply (IHn dl); auto.
(* end assert d = Gfun fd *)
subst d.
clear H5.
clear - RANGE H2 H1 H Hm.
unfold Genv.init_mem in Hm.
forget (Genv.globalenv prog) as ge.
change (AST.prog_defs prog) with (prog_defs prog) in Hm.
forget (prog_defs prog) as dl.
rewrite <- (rev_involutive dl) in H1,Hm.
rewrite nth_error_rev in H1.
2 : {
  rewrite rev_length. clear - RANGE.
  destruct RANGE.
  apply inj_lt_iff. rewrite Coqlib.nat_of_Z_eq by omega. omega. }
rename H1 into H5.
replace (length (rev dl) - nat_of_Z (Z.pos b - 1) - 1)%nat
  with (length (rev dl) - nat_of_Z (Z.pos b))%nat in H5.
2 : { rewrite rev_length.
  clear - RANGE.
  replace (nat_of_Z (Z.pos b-1)) with (nat_of_Z (Z.pos b) - 1)%nat.
  assert (nat_of_Z (Z.pos b) <= length dl)%nat.
  destruct RANGE.
  apply inj_le_iff. rewrite Coqlib.nat_of_Z_eq by omega. auto.
  assert (nat_of_Z (Z.pos b) > 0)%nat. apply inj_gt_iff.
  rewrite Coqlib.nat_of_Z_eq by omega.  simpl. omega.
  omega. destruct RANGE as [? _].
  apply nat_of_Z_lem1.
  assert (nat_of_Z (Z.pos b) > 0)%nat. apply inj_gt_iff. simpl.
  pose proof (Pos2Nat.is_pos b); omega.
  omega. }
assert (0 < nat_of_Z (Z.pos b) <= length dl)%nat.
{ clear - RANGE.
  destruct RANGE; split.
  apply inj_lt_iff. rewrite Coqlib.nat_of_Z_eq; try omega. simpl. auto.
  apply inj_le_iff. rewrite Coqlib.nat_of_Z_eq; try omega. }
clear RANGE; rename H0 into RANGE.
unfold nat_of_Z in *. rewrite Z2Nat.inj_pos in *.
rewrite <- rev_length in RANGE.
forget (rev dl) as dl'; clear dl; rename dl' into dl.
destruct RANGE.
rewrite alloc_globals_rev_eq in Hm.
revert m Hm H1 H5; induction dl; intros.
inv H5.
simpl in H1,Hm.
invSome.
specialize (IHdl _ Hm).
destruct (eq_dec (Pos.to_nat b) (S (length dl))).
+ rewrite e, minus_diag in H5. simpl in H5.
  inversion H5; clear H5; subst a.
  apply alloc_globals_rev_nextblock in Hm.
  rewrite Zlength_correct in Hm.
  rewrite <- inj_S in Hm. rewrite <- e in Hm.
  rewrite positive_nat_Z in Hm.  rewrite Pos2Z.id in Hm.
  subst b.
  clear IHdl H1 H0. clear dl e.
  unfold Genv.alloc_global in H6.
  revert H6; case_eq (alloc m0 0 1); intros.
  unfold drop_perm in H6.
  destruct (range_perm_dec m1 b 0 1 Cur Freeable).
  unfold max_access_at, access_at; inv H6.
  simpl. apply alloc_result in H0. subst b.
  rewrite PMap.gss.
  simpl. auto.
  inv H6.
+ destruct IHdl.
  omega.
  replace (length (a::dl) - Pos.to_nat b)%nat with (S (length dl - Pos.to_nat b))%nat in H5.
  apply H5.
  simpl. destruct (Pos.to_nat b); omega.
  assert (b < nextblock m0)%positive.
  { apply alloc_globals_rev_nextblock in Hm.
    rewrite Zlength_correct in Hm. clear - Hm n H1.
    rewrite Hm.
    apply Pos2Nat.inj_lt.
    pattern Pos.to_nat at 1; rewrite <- Z2Nat.inj_pos.
    rewrite Z2Pos.id by omega.
    rewrite Z2Nat.inj_succ by omega.
    rewrite Nat2Z.id. omega. }
  destruct (alloc_global_old _ _ _ _ H6 (b,0)) as [? ?]; auto.
  unfold max_access_at.
  rewrite <- H8.
  split; auto.
Qed.

Definition initial_jm_ext {Z} (ora : Z) (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G) : juicy_mem :=
  initial_mem m (initial_core_ext ora (Genv.globalenv prog) G n)
           (initial_core_ext_ok _ _ _ _ m H1 H2 H).

Require Import VST.veric.ghost_PCM.
Lemma initial_jm_ext_eq : forall {Z} (ora : Z) (prog: program) m (G: funspecs) (n: nat)
        (H: Genv.init_mem prog = Some m)
        (H1: list_norepet (prog_defs_names prog))
        (H2: match_fdecs (prog_funct prog) G),
  join (m_phi (initial_jm prog m G n H H1 H2))
       (set_ghost (core (m_phi (initial_jm prog m G n H H1 H2))) (Some (ext_ghost ora, NoneP) :: nil) eq_refl)
       (m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
  intros.
  apply resource_at_join2.
  - simpl.
    rewrite !inflate_initial_mem_level.
    unfold initial_core, initial_core_ext; rewrite !level_make_rmap; auto.
  - unfold set_ghost; rewrite level_make_rmap.
    rewrite level_core.
    simpl.
    rewrite !inflate_initial_mem_level.
    unfold initial_core, initial_core_ext; rewrite !level_make_rmap; auto.
  - intros.
    unfold set_ghost; rewrite resource_at_make_rmap, <- core_resource_at.
    simpl.
    unfold initial_core, initial_core_ext, inflate_initial_mem.
    rewrite !resource_at_make_rmap.
    unfold inflate_initial_mem'.
    rewrite !resource_at_make_rmap.
    apply join_comm, core_unit.
  - unfold set_ghost; rewrite ghost_of_make_rmap.
    simpl.
    unfold initial_core, initial_core_ext, inflate_initial_mem.
    rewrite !ghost_of_make_rmap.
    constructor.
Qed.

(* 
Definition prog_vars (p: program) := prog_vars' (prog_defs p).
*)
Notation prog_vars := (@prog_vars function).

Lemma initial_jm_without_locks prog m G n H H1 H2:
  no_locks (m_phi (initial_jm prog m G n H H1 H2)).
Proof.
  simpl.
  unfold inflate_initial_mem; simpl.
  match goal with |- context [ proj1_sig ?a ] => destruct a as (phi & lev & E & ?) end; simpl.
  unfold inflate_initial_mem' in E.
  unfold resource_at in E.
  unfold no_locks, "@"; intros.
  rewrite E.
  destruct (access_at m addr); [ |congruence].
  destruct p; try congruence.
  destruct (fst ((snd (unsquash (initial_core (Genv.globalenv prog) G n)))) addr);
  congruence.
Qed.

Lemma initial_jm_ext_without_locks {Z} (ora : Z) prog m G n H H1 H2:
  no_locks (m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
  simpl.
  unfold inflate_initial_mem; simpl.
  match goal with |- context [ proj1_sig ?a ] => destruct a as (phi & lev & E & ?) end; simpl.
  unfold inflate_initial_mem' in E.
  unfold resource_at in E.
  unfold no_locks, "@"; intros.
  rewrite E.
  destruct (access_at m addr); try congruence.
  destruct p; try congruence.
  destruct (fst ((snd (unsquash (initial_core_ext ora (Genv.globalenv prog) G n)))) addr);
   congruence.
Qed.

(* Specialization of stuff in initial_world:
Lemma level_initial_core ge G n : level (initial_core ge G n) = n.
Proof.
  apply level_make_rmap.
Qed.*)

Definition matchfunspecs (ge : genv) (G : funspecs) (Phi : rmap) : Prop :=
  forall (b : block) fsig cc A P Q,
    func_at'' fsig cc A P Q (b, 0%Z) Phi ->
    exists id P' Q' P'_ne Q'_ne,
      Genv.find_symbol ge id = Some b /\
      find_id id G = Some (mk_funspec fsig cc A P' Q' P'_ne Q'_ne) /\
      cond_approx_eq (level Phi) A P P' /\
      cond_approx_eq (level Phi) A Q Q'.

Lemma initial_jm_matchfunspecs prog m G n H H1 H2:
  matchfunspecs (globalenv prog) G (m_phi (initial_jm prog m G n H H1 H2)).
Proof.
  simpl.
  unfold inflate_initial_mem; simpl.
  match goal with |- context [ proj1_sig ?a ] => destruct a as (phi & lev & E & ?) end; simpl.
  unfold inflate_initial_mem' in E.
  unfold resource_at in E.
  intros b fsig cc A P Q FAT.
  unfold func_at'' in *.
  rewrite level_initial_core in lev.

  set (pp := SomeP _ _) in FAT.
  assert (Pi :
            initial_core (Genv.globalenv prog) G n @ (b, 0)
            = PURE (FUN fsig cc) (preds_fmap (approx n) (approx n) pp)).
  {
    simpl in FAT.
    pose proof FAT as E2.
    unfold "@" in *.
    rewrite E in FAT.
    destruct (access_at m (b, 0)) as [[]|]; simpl in E2; try congruence.
    set (r := fst ( _) _) in FAT at 2.
    destruct (fst ( (snd (unsquash (initial_core (Genv.globalenv prog) G n)))) (b, 0))
      as [t | t p k p0 | k p] eqn:E'''; simpl in E2; try congruence.
    subst r.
    injection FAT as -> ->; f_equal. subst pp. f_equal.
    simpl. f_equal.
    repeat extensionality.
    repeat (f_equal; auto).
  }

  clear -Pi lev.

  unfold initial_core in *.
  rewrite resource_at_make_rmap in Pi.
  unfold initial_core' in *.
  if_tac in Pi. 2:tauto.
  simpl fst in Pi.
  unfold fundef in *.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b) as [i|] eqn:Eb. 2: congruence.
  destruct (find_id i G) as [f0 |] eqn:Ei. 2:congruence.
  destruct f0 as [f1 c0 A0 P0 Q0 P_ne0 Q_ne0].

  subst pp.
  injection Pi as <- -> -> EE.
  apply inj_pair2 in EE.
  apply Genv.invert_find_symbol in Eb.
  unfold filter_genv in *.
  exists i, P0, Q0, P_ne0, Q_ne0.
  split. assumption.
  split. assumption.
  subst n.

  constructor.
  all: intros ts.
  all: apply equal_f_dep with (x := ts) in EE.
  all: extensionality a.
  all: apply equal_f_dep with (x := a) in EE.

  1: apply equal_f_dep with (x := true) in EE.
  2: apply equal_f_dep with (x := false) in EE.

  all: extensionality ge.
  all: apply equal_f_dep with (x := ge) in EE.
  all: simpl in *.
  all: symmetry; rewrite (* Epp',  *)<-EE.
  all: reflexivity.
Qed.

Lemma initial_jm_ext_matchfunspecs {Z} (ora : Z) prog m G n H H1 H2:
  matchfunspecs (globalenv prog) G (m_phi (initial_jm_ext ora prog m G n H H1 H2)).
Proof.
  simpl.
  unfold inflate_initial_mem; simpl.
  match goal with |- context [ proj1_sig ?a ] => destruct a as (phi & lev & E & ?) end; simpl.
  unfold inflate_initial_mem' in E.
  unfold resource_at in E.
  intros b fsig cc A P Q FAT.
  unfold func_at'' in *.
  unfold initial_core_ext in lev; rewrite level_make_rmap in lev.

  set (pp := SomeP _ _) in FAT.
  assert (Pi :
            initial_core_ext ora (Genv.globalenv prog) G n @ (b, 0)
            = PURE (FUN fsig cc) (preds_fmap (approx n) (approx n) pp)).
  {
    simpl in FAT.
    pose proof FAT as E2.
    unfold "@" in *.
    rewrite E in FAT.
    destruct (access_at m (b, 0)) as [[]|]; simpl in E2; try congruence.
    set (r := fst ( _) _) in FAT at 2.
    destruct (fst ( (snd (unsquash (initial_core_ext ora (Genv.globalenv prog) G n)))) (b, 0))
      as [t | t p k p0 | k p] eqn:E'''; simpl in E2; try congruence.
    subst r.
    injection FAT as -> ->; f_equal. subst pp. f_equal.
    simpl. f_equal.
    repeat extensionality.
    repeat (f_equal; auto).
  }

  clear -Pi lev.

  unfold initial_core_ext in *.
  rewrite resource_at_make_rmap in Pi.
  unfold initial_core' in *.
  if_tac in Pi. 2:tauto.
  simpl fst in Pi.
  unfold fundef in *.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b) as [i|] eqn:Eb. 2: congruence.
  destruct (find_id i G) as [f0 |] eqn:Ei. 2:congruence.
  destruct f0 as [f1 c0 A0 P0 Q0 P_ne0 Q_ne0].

  subst pp.
  injection Pi as <- -> -> EE.
  apply inj_pair2 in EE.
  apply Genv.invert_find_symbol in Eb.
  unfold filter_genv in *.
  exists i, P0, Q0, P_ne0, Q_ne0.
  split. assumption.
  split. assumption.
  subst n.

  constructor.
  all: intros ts.
  all: apply equal_f_dep with (x := ts) in EE.
  all: extensionality a.
  all: apply equal_f_dep with (x := a) in EE.

  1: apply equal_f_dep with (x := true) in EE.
  2: apply equal_f_dep with (x := false) in EE.

  all: extensionality ge.
  all: apply equal_f_dep with (x := ge) in EE.
  all: simpl in *.
  all: symmetry; rewrite (* Epp',  *)<-EE.
  all: reflexivity.
Qed.
