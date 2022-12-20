Require Import VST.floyd.base.
Require Import VST.floyd.PTops.
Import compcert.lib.Maps.

Module QP.

Record composite : Type := {
  co_su: struct_or_union;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_ha: Z;
  co_la: legal_alignas_obs
}.

Definition composite_env : Type := PTree.t composite.

Inductive builtin := mk_builtin: external_function -> typelist -> type -> calling_convention -> builtin.

Record program (F: Type) : Type := {
  prog_builtins: list (ident * builtin);
  prog_defs: PTree.t (globdef (fundef F) type);
  prog_public: list ident;
  prog_main: ident;
  prog_comp_env: composite_env
}.

Arguments prog_builtins {F} _.
Arguments prog_defs {F} _.
Arguments prog_public {F} _.
Arguments prog_main {F} _.
Arguments prog_comp_env {F} _.
End QP.

Definition QPcomposite_of_composite (c: composite) (ha: Z) (la: legal_alignas_obs) :=
   {| QP.co_su := c.(co_su);
      QP.co_members := c.(co_members);
      QP.co_attr := c.(co_attr);
      QP.co_sizeof := c.(co_sizeof);
      QP.co_alignof := c.(co_alignof);
      QP.co_rank := c.(co_rank);
      QP.co_ha := ha;
      QP.co_la := la
   |}.

Definition QPcomposite_OK (c: QP.composite) :=
   QP.co_sizeof c >= 0 /\
   (exists n, QP.co_alignof c = two_power_nat n) /\
   (QP.co_alignof c | QP.co_sizeof c).

Definition composite_of_QPcomposite (c: QP.composite)
  (H: QPcomposite_OK c) :=
 {| co_su := c.(QP.co_su);
    co_members := c.(QP.co_members);
    co_attr := c.(QP.co_attr);
    co_sizeof := c.(QP.co_sizeof);
    co_alignof := c.(QP.co_alignof);
    co_rank := c.(QP.co_rank);
    co_sizeof_pos := proj1 H;
    co_alignof_two_p := proj1 (proj2 H);
    co_sizeof_alignof := proj2 (proj2 H)
 |}.

Definition QPcomposite_bogus: QP.composite :=
 QP.Build_composite Struct nil noattr 0 0 0 0 true.

Definition QPcomposite_env_of_composite_env :
     composite_env -> PTree.t Z -> PTree.t legal_alignas_obs-> QP.composite_env :=
 PTree_map3 QPcomposite_of_composite QPcomposite_bogus.

Definition QPcomposite_env_OK: QP.composite_env -> Prop :=
  PTree_Forall QPcomposite_OK.

Lemma QPcomposite_of_composite_OK: 
  forall c ha la, QPcomposite_OK (QPcomposite_of_composite c ha la).
Proof.
intros.
split3; simpl.
apply co_sizeof_pos.
apply co_alignof_two_p.
apply co_sizeof_alignof.
Qed.

Lemma QPcomposite_env_of_composite_env_OK:
  forall (ce: composite_env) ha_env la_env,
     PTree_samedom ce ha_env ->
     PTree_samedom ce la_env ->
    QPcomposite_env_OK (QPcomposite_env_of_composite_env ce ha_env la_env).
Proof.
intros.
red.
rewrite <- PTree_Forall_get_eq.
intro i.
unfold QPcomposite_env_of_composite_env.
rewrite PTree_gmap3 by auto.
destruct ( ce ! i) eqn:?H; simpl; auto.
+
  destruct (proj1 (PTree_domain_eq_e H _) (ex_intro _ _ H1)).
  rewrite H2.
  destruct (proj1 (PTree_domain_eq_e H0 _) (ex_intro _ _ H1)).
  rewrite H3.
  apply QPcomposite_of_composite_OK.
+
 destruct (ha_env ! i); auto.
 destruct (la_env ! i); auto. 
Qed.

Fixpoint QP_list_helper 
  (al: list (positive * QP.composite))
  (H: Forall (fun ix => QPcomposite_OK (snd ix)) al) :  list (positive * composite).
destruct al as [ | [i c] al].
apply nil.
apply cons.
split. apply i. eapply composite_of_QPcomposite.
apply Forall_inv in H. apply H.
apply (QP_list_helper al).
eapply Forall_inv_tail.
apply H.
Defined.

Lemma QP_list_helper_ext:
  forall al bl H H', 
   al=bl -> QP_list_helper al H = QP_list_helper bl H'.
Proof.
induction al; destruct bl; intros; auto; inv H0.
destruct p.
simpl.
f_equal.
f_equal. f_equal.
f_equal. apply proof_irr.
auto.
Qed.


Definition composite_env_of_QPcomposite_env'
   (ce: QP.composite_env)
   (H: QPcomposite_env_OK ce) : composite_env :=
 PTree_Properties.of_list
   (QP_list_helper _ (proj1 (PTree_Forall_elements _ _ _) H)).

Fixpoint ce_of_QPce'
   (ce: PTree.tree' QP.composite) :
   PTree_Forall' QPcomposite_OK ce -> PTree.tree' composite := 
match ce as t return (PTree_Forall' QPcomposite_OK t -> PTree.tree' composite) with
| PTree.Node001 r => fun H => PTree.Node001 (ce_of_QPce' r H)
| PTree.Node010 x => fun H => PTree.Node010 (composite_of_QPcomposite x H)
| PTree.Node011 x r => fun H => PTree.Node011 (composite_of_QPcomposite x (proj1 H)) (ce_of_QPce' r (proj2 H))
| PTree.Node100 l => fun H => PTree.Node100 (ce_of_QPce' l H)
| PTree.Node101 l r => fun H => PTree.Node101 (ce_of_QPce' l (proj1 H)) (ce_of_QPce' r (proj2 H))
| PTree.Node110 l x => fun H => PTree.Node110 (ce_of_QPce' l (proj1 H)) (composite_of_QPcomposite x (proj2 H))
| PTree.Node111 l x r => fun H => PTree.Node111
     (ce_of_QPce' l (proj1 H)) (composite_of_QPcomposite x (proj1 (proj2 H)))
            (ce_of_QPce' r (proj2 (proj2 H)))
end.

Definition composite_env_of_QPcomposite_env
   (ce: QP.composite_env)
   (H: QPcomposite_env_OK ce) : composite_env :=
match
  ce as t
  return
    (match t with
     | PTree.Empty => True
     | PTree.Nodes m' => PTree_Forall' QPcomposite_OK m'
     end -> composite_env)
with
| PTree.Empty => fun _ : True => PTree.Empty
| PTree.Nodes m =>
    fun H0 : PTree_Forall' QPcomposite_OK m =>
    PTree.Nodes (ce_of_QPce' m H0)
end H.

Lemma composite_env_of_QPcomposite_env'_eq:
 forall ce H i,
  PTree.get i (composite_env_of_QPcomposite_env' ce H) = 
  PTree.get i (composite_env_of_QPcomposite_env ce H).
Proof.
intros.
unfold composite_env_of_QPcomposite_env'.
destruct ((PTree_Properties.of_list
   (QP_list_helper (PTree.elements ce)
      (proj1 (PTree_Forall_elements QP.composite QPcomposite_OK ce)
         H))) ! i) eqn:?H.
-
apply PTree_Properties.in_of_list in H0.
assert (exists c' H', 
  In (i,c') (PTree.elements ce) /\ c = composite_of_QPcomposite c' H'). {
 pose proof (PTree.elements_keys_norepet ce).
 set (H2 := proj1 _ _) in H0.
 clearbody H2.
 revert H0 H1; induction (PTree.elements ce) as [|[??]]; intros.
 inv H0.
 specialize (IHl (Forall_inv_tail H2)).
 simpl in *.
 inv H1.
 destruct H0. inv H0.
 exists c0.
 exists (Forall_inv H2).
 split; auto.
 destruct (IHl H0 H6) as [c' [? ?]].
 destruct H1.
 exists c', x; split; auto.
}
set (H2 := proj1 _ _) in H0. clearbody H2.
destruct H1 as [c' [? [? ?]]].
subst.
rename x into Hc'.
pose proof (PTree.elements_complete _ _ _ H1).
clear - c' H3.
destruct ce as [|ce]. inv H3.
unfold PTree.get in *.
revert i H3; induction ce; destruct i; simpl; intros; try discriminate;
try (apply IHce; auto);
try (apply IHce2; auto);
try (apply IHce1; auto);
try (inv H3; f_equal; f_equal; apply proof_irr).
-
symmetry.
set (H2 := proj1 _ _) in H0.
clearbody H2.
assert (ce ! i = None).
destruct (ce ! i) eqn:?H; auto.
exfalso.
apply PTree.elements_correct in H1.
assert (In i (map fst  (QP_list_helper (PTree.elements ce) H2))). {
 clear - H1; induction (PTree.elements ce) as [|[??]].
 inv H1.
 specialize (IHl (Forall_inv_tail H2)).
 destruct H1. inv H. left; reflexivity.
 right; auto.
}
apply PTree_Properties.of_list_dom in H3.
destruct H3. congruence.
clear - H1.
hnf in H.
destruct ce as [|ce]; simpl; auto.
unfold PTree.get in *.
revert i H H1; induction ce; destruct i; simpl; intros; auto;
try discriminate.
Qed.

Lemma composite_of_QPcomposite_of_composite:
  forall c ha la H, composite_of_QPcomposite (QPcomposite_of_composite c ha la) H = c.
Proof.
intros.
destruct c; simpl.
unfold composite_of_QPcomposite.
f_equal; simpl; auto; apply proof_irr.
Qed.

Lemma QPcomposite_of_composite_of_QPcomposite:
  forall c H, QPcomposite_of_composite
                            (composite_of_QPcomposite c H) (QP.co_ha c) (QP.co_la c) = c.
Proof.
intros.
destruct c; simpl.
unfold composite_of_QPcomposite.
simpl.
unfold QPcomposite_of_composite.
simpl.
f_equal; simpl; auto; apply proof_irr.
Qed.


Lemma composite_env_of_QPcomposite_env_of_composite_env:
 forall (ce: composite_env) ha la OK
 (HA: PTree_samedom ce ha)
 (LA: PTree_samedom ce la),
   (composite_env_of_QPcomposite_env
    (QPcomposite_env_of_composite_env ce ha la) OK) =
   ce.
Proof.
destruct ce as [|ce]; destruct ha as [|ha]; destruct la as [|la].
all: try solve [simpl; intros; auto; try contradiction].
intros.
red in HA, LA.
unfold QPcomposite_env_of_composite_env.
unfold composite_env_of_QPcomposite_env.
unfold PTree_map3. f_equal.
red in OK. red in OK.
simpl in OK.
revert ha HA la LA OK.
induction ce; destruct ha; intro HA; try destruct HA;
 destruct la; intro LA; try destruct LA;
simpl in *; intros; f_equal; auto;
apply composite_of_QPcomposite_of_composite.
Qed.

Lemma QPcomposite_env_of_composite_env_of_QPcomposite_env:
 forall (ce: QP.composite_env)
   (H : QPcomposite_env_OK ce),
   (QPcomposite_env_of_composite_env
    (composite_env_of_QPcomposite_env ce H)
    (PTree.map1 QP.co_ha ce)
    (PTree.map1 QP.co_la ce)) =
  ce.
Proof.
destruct ce as [|ce]; simpl; intros; auto.
f_equal.
revert H; induction ce; simpl; intros; f_equal;
eauto;
apply QPcomposite_of_composite_of_QPcomposite.
Qed.

Lemma QPcomposite_of_composite_inj: forall c1 ha1 la1 c2 ha2 la2, 
  QPcomposite_of_composite c1 ha1 la1 = QPcomposite_of_composite c2 ha2 la2 ->
    c1=c2 /\ ha1=ha2 /\ la1=la2.
Proof.
intros.
destruct c1, c2; inv H; simpl in *; split3; f_equal; auto; apply proof_irr.
Qed.

Lemma Some_inj: forall {A} (x y: A), Some x = Some y -> x=y.
Proof. intros. inv H; auto. Qed.


Lemma samedom_ha_composite_env_of_QPcomposite_env:
 forall ce OK, 
  PTree_samedom (composite_env_of_QPcomposite_env ce OK)
     (PTree.map1 QP.co_ha ce).
Proof.
intros.
destruct ce as [|ce]. apply I.
red.
simpl.
revert OK; induction ce; simpl; intros; auto.
Qed.

Lemma samedom_la_composite_env_of_QPcomposite_env:
 forall ce OK, 
  PTree_samedom (composite_env_of_QPcomposite_env ce OK)
     (PTree.map1 QP.co_la ce).
Proof.
intros.
destruct ce as [|ce]. apply I.
red.
simpl.
revert OK; induction ce; simpl; intros; auto.
Qed.

Lemma get_composite_env_of_QPcomposite_env:
 forall ce OK i co,
  (composite_env_of_QPcomposite_env ce OK) ! i = Some co 
<-> exists ha, exists la, 
  ce ! i = Some (QPcomposite_of_composite co ha la). 
Proof.
 intros.
 rewrite <- composite_env_of_QPcomposite_env'_eq.
 split; intro.
-
 assert (H3: ce ! i <> None). {
 intro. unfold composite_env_of_QPcomposite_env' in H.
 set (H1 := proj1 _) in H. set (H2 := H1 OK) in H. clearbody H2; clear H1.
 apply PTree_Properties.in_of_list in H.
 assert (In i (map fst (PTree.elements ce))).
 revert H2 H; clear; induction (PTree.elements ce) as [|[??]]; simpl; intros; auto.
 destruct H. inv H. auto. right. apply (IHl (Forall_inv_tail H2)); auto.
 apply list_in_map_inv in H1. destruct H1 as [[??] [??]]; subst.
 simpl in H0. apply PTree.elements_complete in H3. congruence.
 }
 pose proof (QPcomposite_env_of_composite_env_of_QPcomposite_env _ OK).
 rewrite <- H0.
 destruct (ce ! i) eqn:?H; try congruence; clear H3. clear H0.
 unfold QPcomposite_env_of_composite_env.
 rewrite PTree_gmap3.
 rewrite <- composite_env_of_QPcomposite_env'_eq. 
 rewrite H.  rewrite !PTree.gmap1. unfold option_map; rewrite H1.
 eauto. 
 apply samedom_ha_composite_env_of_QPcomposite_env.
 apply samedom_la_composite_env_of_QPcomposite_env.
-
 destruct H as [ha [la ?]].
 pose proof (QPcomposite_env_of_composite_env_of_QPcomposite_env _ OK).
 rewrite <- H0 in H; clear H0.
 unfold QPcomposite_env_of_composite_env in H.
 rewrite PTree_gmap3 in H; unfold option_map in H.
 rewrite <- composite_env_of_QPcomposite_env'_eq in H.
 destruct ( (composite_env_of_QPcomposite_env' ce OK) ! i); try discriminate.
 destruct ((PTree.map1 QP.co_ha ce) ! i); try discriminate.
 destruct ((PTree.map1 QP.co_la ce) ! i); try discriminate.
 apply Some_inj in H; apply QPcomposite_of_composite_inj in H; f_equal; tauto.
 destruct ((PTree.map1 QP.co_ha ce) ! i); try discriminate.
 destruct ((PTree.map1 QP.co_la ce) ! i); try discriminate.
 apply samedom_ha_composite_env_of_QPcomposite_env.
 apply samedom_la_composite_env_of_QPcomposite_env.
Qed.

Definition QPcompspecs_OK (ce: QP.composite_env) :=
  {H: QPcomposite_env_OK ce &
       let ce' := composite_env_of_QPcomposite_env ce H in
       let ha' := (PTree.map1 QP.co_ha ce) in
       let la' := (PTree.map1 QP.co_la ce) in
       composite_env_consistent ce' /\
       composite_env_legal_fieldlist ce' /\
       composite_env_complete_legal_cosu_type ce' /\
       hardware_alignof_env_consistent ce' ha' /\
       legal_alignas_env_consistent ce' ha' la' /\
       legal_alignas_env_sound ce' ha' la'
  }.

Lemma hardware_alignof_env_completeQP:
 forall ce H, hardware_alignof_env_complete 
                    (composite_env_of_QPcomposite_env ce H) (PTree.map1 QP.co_ha ce).
Proof.
intros.
hnf; intros; split; intros [? ?].
rewrite get_composite_env_of_QPcomposite_env in H0.
destruct H0 as [? [? ?]].
rewrite PTree.gmap1, H0. simpl. eauto.
rewrite PTree.gmap1 in H0; unfold option_map in H0.
destruct (ce ! i) eqn:?H; inv H0.
pose proof H. red in H0. rewrite <- PTree_Forall_get_eq in H0.
specialize (H0 i). rewrite H1 in H0.
exists (composite_of_QPcomposite _ H0).
rewrite get_composite_env_of_QPcomposite_env.
do 2 eexists.
rewrite QPcomposite_of_composite_of_QPcomposite.
assumption.
Qed.


Lemma legal_alignas_env_completeQP:
 forall ce H, legal_alignas_env_complete 
                    (composite_env_of_QPcomposite_env ce H) (PTree.map1 QP.co_la ce).
Proof.
intros.
hnf; intros; split; intros [? ?].
rewrite get_composite_env_of_QPcomposite_env in H0.
destruct H0 as [? [? ?]].
rewrite PTree.gmap1, H0. simpl. eauto.
rewrite PTree.gmap1 in H0; unfold option_map in H0.
destruct (ce ! i) eqn:?H; inv H0.
pose proof H. red in H0. rewrite <- PTree_Forall_get_eq in H0.
specialize (H0 i). rewrite H1 in H0.
exists (composite_of_QPcomposite _ H0).
rewrite get_composite_env_of_QPcomposite_env.
do 2 eexists.
rewrite QPcomposite_of_composite_of_QPcomposite.
assumption.
Qed.

Definition compspecs_of_QPcomposite_env ce (H: QPcompspecs_OK ce) : compspecs
  := 
match H with
|  existT H0 (conj H1 (conj H3 (conj H5 (conj H7 (conj H9 H10))))) =>
    let ce' := composite_env_of_QPcomposite_env ce H0 in
    let ha' := PTree.map1 QP.co_ha ce in
    let la' := PTree.map1 QP.co_la ce in
    {|
    cenv_cs := ce';
    cenv_consistent := H1;
    cenv_legal_fieldlist := H3;
    cenv_legal_su := H5;
    ha_env_cs := ha';
    ha_env_cs_consistent := H7;
    ha_env_cs_complete := hardware_alignof_env_completeQP ce H0;
    la_env_cs := la';
    la_env_cs_consistent := H9;
    la_env_cs_complete := legal_alignas_env_completeQP ce H0;
    la_env_cs_sound := H10 |}
end.

Definition QPcomposite_eq (c d: QP.composite) : bool :=
 (eqb_su c.(QP.co_su) d.(QP.co_su) 
 && eqb_list eqb_member c.(QP.co_members) d.(QP.co_members)
 && eqb_attr c.(QP.co_attr) d.(QP.co_attr)
 && Z.eqb c.(QP.co_sizeof) d.(QP.co_sizeof)
 && Z.eqb c.(QP.co_alignof) d.(QP.co_alignof)
 && Nat.eqb c.(QP.co_rank) d.(QP.co_rank)
 && Z.eqb c.(QP.co_ha) d.(QP.co_ha)
 && Bool.eqb c.(QP.co_la) d.(QP.co_la))%bool.

Lemma QPcomposite_eq_e:
 forall c1 c2, QPcomposite_eq c1 c2 = true -> c1=c2.
Proof.
intros.
unfold QPcomposite_eq in H.
 repeat rewrite andb_true_iff in H; decompose [and] H; clear H.
 apply eqb_su_spec in H0.
 apply eqb_list_spec in H8; [ | intros; apply eqb_member_spec].
 apply eqb_attr_spec in H7.
 apply Z.eqb_eq in H3.
 apply Z.eqb_eq in H5.
 apply Z.eqb_eq in H6.
 apply Nat.eqb_eq in H4.
 apply eqb_prop in H1.
 destruct c1,c2; simpl in *;  congruence.
Qed.

Lemma complete_legal_cosu_stable:
    forall env env' : composite_env,
       (forall (id : positive) (co : composite),
        env ! id = Some co -> env' ! id = Some co) ->
  forall m, composite_complete_legal_cosu_type env m = true ->
          composite_complete_legal_cosu_type env' m = true.
Proof.
  induction m; simpl; intros.
  auto.
  InvBooleans.
  apply IHm in H2; clear IHm.
  rewrite andb_true_iff; split; auto.
  induction (type_member a); simpl in H1|-*; auto.
  destruct (env ! i) eqn:?H; try discriminate; rewrite (H _ _ H0); auto.
  destruct (env ! i) eqn:?H; try discriminate; rewrite (H _ _ H0); auto.
Qed.

Lemma sizeof_type_stable':
  forall env1 env t,
     (forall id co,   env1 ! id = Some co -> env ! id = Some co) ->
    @complete_legal_cosu_type env1 t = true ->
    @Ctypes.sizeof env1 t = @Ctypes.sizeof env t.
Proof.
induction t; simpl; intros; auto.
f_equal; auto.
destruct (env1 ! i) eqn:?H; try discriminate.
rewrite (H _ _ H1). auto.
destruct (env1 ! i) eqn:?H; try discriminate.
rewrite (H _ _ H1). auto.
Qed.

Lemma hardware_alignof_type_stable': 
  forall  (env' env : composite_env)
     (H:  forall id co,   env' ! id = Some co -> env ! id = Some co)
     (ha_env ha_env' : PTree.t Z)
     (H0: forall id  ofs,   ha_env' ! id = Some ofs -> ha_env ! id = Some ofs)
     (H0: PTree_samedom env' ha_env'),
     forall t, complete_type env' t = true ->
       hardware_alignof ha_env' t = hardware_alignof ha_env t.
Proof.
induction t; simpl; intros; auto.
destruct (env' ! i) eqn:?H; try discriminate.
destruct (proj1 (PTree_domain_eq_e H1 i)); eauto.
rewrite H4. rewrite (H0 _ _ H4). auto.
destruct (env' ! i) eqn:?H; try discriminate.
destruct (proj1 (PTree_domain_eq_e H1 i)); eauto.
rewrite H4. rewrite (H0 _ _ H4). auto.
Qed.

Lemma field_offset_stable'':
    forall (env1 env : PTree.t composite),
       composite_env_consistent env1 ->
       (forall id co, env1 ! id = Some co -> env ! id = Some co) ->
       forall i co,
       env1 ! i = Some co ->
       forall j,
       field_offset env1 j (co_members co) = 
       field_offset env j (co_members co).
Proof.
intros.
pose proof (co_consistent_complete _ _ (H _ _ H1)).
symmetry; apply field_offset_stable; auto.
Qed. 

Lemma align_compatible_rec_stable':
 forall (env1 env: composite_env)
    (CONS: composite_env_consistent env1)
    (COSU: composite_env_complete_legal_cosu_type env1)
    (S: forall id co, env1 ! id = Some co -> env ! id = Some co)
   t ofs
   (H9a: @complete_legal_cosu_type env1 t = true) 
   (H: align_compatible_rec env1 t ofs),
  align_compatible_rec env t ofs.
Proof.
  intros until t.
  type_induction.type_induction t env1 CONS; intros;
  intros; inv H;
  try (eapply align_compatible_rec_by_value; [eassumption | auto]).
 +
    simpl in H9a.
    apply align_compatible_rec_Tarray.
    intros.
    rewrite <- (sizeof_type_stable' _ _ _ S H9a).
    apply IH; auto.
 +
   clear H9a.
   rewrite H2 in IH.
   eapply align_compatible_rec_Tstruct. apply S; eassumption. auto.
   intros.
   rewrite <-  (field_offset_stable'' _ _ CONS S _ _ H2 i0) in H0.
   specialize (H5 _ _ _ H H0).
   rewrite Forall_forall in IH.
   assert (exists m, In m (co_members co) /\ type_member m = t0). {
    clear - H. induction (co_members co). inv H. simpl in H. if_tac in H. exists a. inv H. simpl; auto. 
    destruct (IHm H) as [m1 [? ?]]. exists m1; simpl; auto.
   }
   destruct H1 as [m [? ?]]. subst t0.
   apply (IH m); auto. clear H1.
   pose proof (COSU  _ _ H2).
   clear - H1 H. induction (co_members co). inv H. simpl in H,H1.
                         InvBooleans.         
                        if_tac in H. inv H. auto.  auto.
 +
   clear H9a.
   rewrite H2 in IH.
   eapply align_compatible_rec_Tunion. apply S; eassumption.  auto.
   intros.
   specialize (H5 _ _ H).
   rewrite Forall_forall in IH.
   assert (exists m, In m (co_members co) /\ type_member m = t0). {
    clear - H. induction (co_members co). inv H. simpl in H. if_tac in H. exists a. inv H. simpl; auto. 
    destruct (IHm H) as [m1 [? ?]]. exists m1; simpl; auto.
   }
   destruct H0 as [m [? ?]]. subst t0.
   apply (IH m); auto.
   apply COSU in H2.
   clear - H2 H0.
   induction (co_members co). inv H0.
   destruct H0. subst. simpl in H2. rewrite andb_true_iff in H2. tauto.
   simpl in H2. rewrite andb_true_iff in H2. tauto.
Qed.

Lemma hardware_alignof_composite_stable:
 forall (ce1 : QP.composite_env)
    (OKce1 : QPcomposite_env_OK ce1)
    (CONSce1 : composite_env_consistent
            (composite_env_of_QPcomposite_env ce1 OKce1))
    (HAce1 : hardware_alignof_env_consistent
          (composite_env_of_QPcomposite_env ce1 OKce1)
          (PTree.map1 QP.co_ha ce1))
    (ce : PTree.t QP.composite)
    (OKce : QPcomposite_env_OK ce)
    (HA1 : forall (i : positive) (ha : Z),
      (PTree.map1 QP.co_ha ce1) ! i = Some ha ->
      (PTree.map1 QP.co_ha ce) ! i = Some ha)
    i c
  (H : (composite_env_of_QPcomposite_env ce OKce) ! i = Some c)
  (H0 : (composite_env_of_QPcomposite_env ce1 OKce1) ! i = Some c),
hardware_alignof_composite (PTree.map1 QP.co_ha ce1) (co_members c) =
hardware_alignof_composite (PTree.map1 QP.co_ha ce) (co_members c).
Proof.
intros.
  pose proof (co_consistent_complete _ _  (CONSce1 _ _ H0)).
  induction (co_members c); simpl; auto.
  simpl in H1; rewrite andb_true_iff in H1; destruct H1.
  f_equal; auto.
  clear - H1 HA1 CONSce1.
  revert H1.
  forget (type_member a) as t.
  type_induction.type_induction t (composite_env_of_QPcomposite_env ce1 OKce1) CONSce1; simpl; intros; auto.
  clear IH.
  destruct ((composite_env_of_QPcomposite_env ce1 OKce1) ! id) eqn:?H; inv H1.
  rewrite get_composite_env_of_QPcomposite_env in H. destruct H as [ha [la ?]].
  specialize (HA1 id ha).
  rewrite !PTree.gmap1 in HA1|-*. unfold option_map in HA1|-*. rewrite H in *.
  specialize (HA1 (eq_refl _)).
  destruct (ce ! id) eqn:?H; inv HA1. reflexivity.
  clear IH.
  destruct ((composite_env_of_QPcomposite_env ce1 OKce1) ! id) eqn:?H; inv H1.
  rewrite get_composite_env_of_QPcomposite_env in H. destruct H as [ha [la ?]].
  specialize (HA1 id ha).
  rewrite !PTree.gmap1 in HA1|-*. unfold option_map in HA1|-*. rewrite H in *.
  specialize (HA1 (eq_refl _)).
  destruct (ce ! id) eqn:?H; inv HA1. reflexivity.
Qed.

Lemma legal_alignas_type_stable:
 forall (ce1 : QP.composite_env)
    (OKce1 : QPcomposite_env_OK ce1)
   (CONSce1 : composite_env_consistent (composite_env_of_QPcomposite_env ce1 OKce1))
   (ce : PTree.t QP.composite)
   (OKce : QPcomposite_env_OK ce)
   (SUB1 : forall (i : positive) (c : composite),
       (composite_env_of_QPcomposite_env ce1 OKce1) ! i = Some c ->
       (composite_env_of_QPcomposite_env ce OKce) ! i = Some c)
   (LA1 : forall (i : positive) (la : legal_alignas_obs),
      (PTree.map1 QP.co_la ce1) ! i = Some la ->
      (PTree.map1 QP.co_la ce) ! i = Some la)
   (t : type)
   (H1 : complete_type (composite_env_of_QPcomposite_env ce1 OKce1) t = true)
   (H4 : forall t : type,
     complete_type (composite_env_of_QPcomposite_env ce1 OKce1) t = true ->
     hardware_alignof (PTree.map1 QP.co_ha ce1) t =
     hardware_alignof (PTree.map1 QP.co_ha ce) t),
legal_alignas_type (composite_env_of_QPcomposite_env ce1 OKce1)
  (PTree.map1 QP.co_ha ce1) (PTree.map1 QP.co_la ce1) t =
legal_alignas_type (composite_env_of_QPcomposite_env ce OKce)
  (PTree.map1 QP.co_ha ce) (PTree.map1 QP.co_la ce) t.
Proof.
intros.
 revert H1;
 type_induction.type_induction t (composite_env_of_QPcomposite_env ce1 OKce1) CONSce1; simpl; intros; auto.
 rewrite H4 by auto.
 rewrite IH by auto.
  rewrite (sizeof_stable _ _ SUB1 _ H1).
 auto.
 clear IH.
 pose proof (proj1 (PTree_domain_eq_e (samedom_la_composite_env_of_QPcomposite_env ce1 OKce1) id)).
 destruct ((composite_env_of_QPcomposite_env ce1 OKce1) ! id) eqn:?H; inv H1.
  spec H; [eauto |]. destruct H.
 unfold legal_alignas_obs in *;  rewrite H.
 rewrite (LA1 _ _ H). auto.
 pose proof (proj1 (PTree_domain_eq_e (samedom_la_composite_env_of_QPcomposite_env ce1 OKce1) id)).
 destruct ((composite_env_of_QPcomposite_env ce1 OKce1) ! id) eqn:?H; inv H1.
 spec H; [eauto |]. destruct H.
 unfold legal_alignas_obs in *;  rewrite H.
 rewrite (LA1 _ _ H). auto.
Qed.

Lemma legal_alignas_composite_stable:
 forall 
  (ce1 : QP.composite_env)
  (OKce1 : QPcomposite_env_OK ce1)
  (CONSce1 : composite_env_consistent
            (composite_env_of_QPcomposite_env ce1 OKce1))
  (HAce1 : hardware_alignof_env_consistent
          (composite_env_of_QPcomposite_env ce1 OKce1)
          (PTree.map1 QP.co_ha ce1))
  (ce : PTree.t QP.composite)
  (OKce : QPcomposite_env_OK ce) 
  (SUB1 : forall (i : positive) (c : composite),
       (composite_env_of_QPcomposite_env ce1 OKce1) ! i = Some c ->
       (composite_env_of_QPcomposite_env ce OKce) ! i = Some c)
  (HA1 : forall (i : positive) (ha : Z),
      (PTree.map1 QP.co_ha ce1) ! i = Some ha ->
      (PTree.map1 QP.co_ha ce) ! i = Some ha)
  (LA1 : forall (i : positive) (la : legal_alignas_obs),
      (PTree.map1 QP.co_la ce1) ! i = Some la ->
      (PTree.map1 QP.co_la ce) ! i = Some la)
  i c
  (H : (composite_env_of_QPcomposite_env ce OKce) ! i = Some c)
  (H0 : (composite_env_of_QPcomposite_env ce1 OKce1) ! i = Some c),
legal_alignas_composite (composite_env_of_QPcomposite_env ce1 OKce1)
  (PTree.map1 QP.co_ha ce1) (PTree.map1 QP.co_la ce1) c =
legal_alignas_composite (composite_env_of_QPcomposite_env ce OKce)
  (PTree.map1 QP.co_ha ce) (PTree.map1 QP.co_la ce) c.
Proof.
intros.
   unfold legal_alignas_composite.
  pose proof (co_consistent_complete _ _  (CONSce1 _ _ H0)).
  destruct (co_su c) eqn:?H.
  *
  forget 0 as ofs.
  revert ofs; induction (co_members c); intros; auto.
  simpl in H1; rewrite andb_true_iff in H1; destruct H1.
  unfold legal_alignas_struct_members_rec.
  fold (legal_alignas_struct_members_rec (composite_env_of_QPcomposite_env ce1 OKce1)
    (@PTree.map1 QP.composite Z QP.co_ha ce1)
    (@PTree.map1 QP.composite legal_alignas_obs QP.co_la ce1)  m).
 fold (legal_alignas_struct_members_rec (composite_env_of_QPcomposite_env _ OKce)
    (@PTree.map1 QP.composite Z QP.co_ha ce)
    (@PTree.map1 QP.composite legal_alignas_obs QP.co_la ce)  m).
  rewrite IHm by auto; clear IHm.
  pose proof (hardware_alignof_type_stable' _ _ SUB1 _ _ HA1).
  spec H4; [apply samedom_ha_composite_env_of_QPcomposite_env | ].
  rewrite !(next_field_stable _ _ SUB1 ofs _ H1).
  f_equal. f_equal.
   2:   eapply legal_alignas_type_stable; eauto.
  unfold legal_alignas_member.
  destruct a; auto.
   rewrite !H4 by auto. f_equal. f_equal. unfold bitalignof. 
  rewrite (alignof_stable _ _ SUB1) by auto. auto.
 *
  induction (co_members c); intros; auto.
  simpl in H1; rewrite andb_true_iff in H1; destruct H1.
  unfold legal_alignas_union_members_rec.
  fold (legal_alignas_union_members_rec (composite_env_of_QPcomposite_env ce1 OKce1)
    (@PTree.map1 QP.composite Z QP.co_ha ce1)
    (@PTree.map1 QP.composite legal_alignas_obs QP.co_la ce1)  m).
 fold (legal_alignas_union_members_rec (composite_env_of_QPcomposite_env _ OKce)
    (@PTree.map1 QP.composite Z QP.co_ha ce)
    (@PTree.map1 QP.composite legal_alignas_obs QP.co_la ce)  m).
 f_equal.
  eapply legal_alignas_type_stable; eauto.
  eapply hardware_alignof_type_stable'; eauto.
  apply samedom_ha_composite_env_of_QPcomposite_env.
  apply IHm; auto.
Qed.

Lemma merged_compspecs':
 forall (ce1 ce2 : QP.composite_env)
    (OK1: QPcompspecs_OK ce1)
    (OK2: QPcompspecs_OK ce2) 
    ce
    (MERGE : merge_consistent_PTrees QPcomposite_eq ce1 ce2 = Errors.OK ce),
    QPcompspecs_OK ce.
Proof.
intros.
 destruct OK1 as [OKce1 [CONSce1 [LFce1 [COSUce1 [HAce1 [LAce1 LASce1]]]]]].
 destruct OK2 as [OKce2 [CONSce2 [LFce2 [COSUce2 [HAce2 [LAce2 LASce2]]]]]].
 assert (OKce: QPcomposite_env_OK ce). {
   clear - OKce1 OKce2 MERGE.
   unfold QPcomposite_env_OK in *; rewrite <- PTree_Forall_get_eq in *.
   intro i; apply (merge_PTrees_e i) in MERGE.
   specialize (OKce1 i). specialize (OKce2 i).
   destruct (ce1 ! i) eqn:?H; auto;
   destruct (ce2 ! i) eqn:?H; auto.
   destruct MERGE as [? [? ?]]. rewrite H2.
   destruct (QPcomposite_eq c c0) eqn:?H; inv H1; auto.
   rewrite MERGE; auto. 
   rewrite MERGE; auto. 
   rewrite MERGE; auto. 
 }
 red.
 exists OKce.
 assert (SUB1: forall i c, (composite_env_of_QPcomposite_env ce1 OKce1) ! i = Some c ->
                      (composite_env_of_QPcomposite_env ce OKce) ! i = Some c). {
 clear - MERGE. intros.
 apply (merge_PTrees_e i) in MERGE.
 rewrite get_composite_env_of_QPcomposite_env in H |- *.
 destruct H as [? [? ?]]. rewrite H in MERGE.
 destruct (ce2 ! i) eqn:?H.
 destruct MERGE as [c' [? ?]].
 destruct (QPcomposite_eq _ _) eqn:?H in H1; inv H1. apply QPcomposite_eq_e in H3; subst. eauto.
 eauto.
}
 assert (SUB2: forall i c, (composite_env_of_QPcomposite_env ce2 OKce2) ! i = Some c ->
                      (composite_env_of_QPcomposite_env ce OKce) ! i = Some c). {
 clear - MERGE. intros.
 apply (merge_PTrees_e i) in MERGE.
 rewrite get_composite_env_of_QPcomposite_env in H |- *.
 destruct H as [? [? ?]]. rewrite H in MERGE.
 destruct (ce1 ! i) eqn:?H.
 destruct MERGE as [c' [? ?]].
 destruct (QPcomposite_eq _ _) eqn:?H in H1; inv H1. apply QPcomposite_eq_e in H3; subst. eauto.
 eauto.
}
 assert (HA1: forall i ha, (PTree.map1 QP.co_ha ce1) ! i = Some ha ->
                      (PTree.map1 QP.co_ha ce) ! i = Some ha). {
 clear - MERGE. intros.
 apply (merge_PTrees_e i) in MERGE.
 rewrite PTree.gmap1 in H |- *; unfold option_map in *.
 destruct (ce1 ! i) eqn:?H; inv H.
 destruct (ce2 ! i) eqn:?H.
 destruct MERGE as [? [? ?]].
 destruct (QPcomposite_eq _ _) eqn:?H in H1; inv H1. rewrite H2; auto. rewrite MERGE; auto.
}
 assert (HA2: forall i ha, (PTree.map1 QP.co_ha ce2) ! i = Some ha ->
                      (PTree.map1 QP.co_ha ce) ! i = Some ha). {
 clear - MERGE. intros.
 apply (merge_PTrees_e i) in MERGE.
 rewrite PTree.gmap1 in H |- *; unfold option_map in *.
 destruct (ce2 ! i) eqn:?H; inv H.
 destruct (ce1 ! i) eqn:?H.
 destruct MERGE as [? [? ?]].
 destruct (QPcomposite_eq c0 c) eqn:?H; inv H1.
 apply QPcomposite_eq_e in H3; subst. rewrite H2; auto.
  rewrite MERGE; auto.
}
 assert (LA1: forall i la, (PTree.map1 QP.co_la ce1) ! i = Some la ->
                      (PTree.map1 QP.co_la ce) ! i = Some la). {
 clear - MERGE. intros.
 apply (merge_PTrees_e i) in MERGE.
 rewrite PTree.gmap1 in H |- *; unfold option_map in *.
 destruct (ce1 ! i) eqn:?H; inv H.
 destruct (ce2 ! i) eqn:?H.
 destruct MERGE as [? [? ?]].
 destruct (QPcomposite_eq _ _) eqn:?H in H1; inv H1. rewrite H2; auto. rewrite MERGE; auto.
}
 assert (LA2: forall i la, (PTree.map1 QP.co_la ce2) ! i = Some la ->
                      (PTree.map1 QP.co_la ce) ! i = Some la). {
 clear - MERGE. intros.
 apply (merge_PTrees_e i) in MERGE.
 rewrite PTree.gmap1 in H |- *; unfold option_map in *.
 destruct (ce2 ! i) eqn:?H; inv H.
 destruct (ce1 ! i) eqn:?H.
 destruct MERGE as [? [? ?]].
 destruct (QPcomposite_eq c0 c) eqn:?H; inv H1.
 apply QPcomposite_eq_e in H3; subst. rewrite H2; auto.
  rewrite MERGE; auto.
}
 split3; [ | | split3; [ | | split]].
 - (* composite_env_consistent *)
 clear - CONSce1 CONSce2 MERGE SUB1 SUB2.
 intros i c ?; assert  (H1 := CONSce1 i c); assert (H2 := CONSce2 i c).
 apply (merge_PTrees_e i) in MERGE.
 rewrite get_composite_env_of_QPcomposite_env in H.
 rewrite get_composite_env_of_QPcomposite_env in H1, H2.
 destruct H as [? [? ?]].
 rewrite H in MERGE.
 destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
 destruct MERGE as [c' [? ?]].
 destruct (QPcomposite_eq c0 c1) eqn:?H in H4; inv H4. apply QPcomposite_eq_e in H6; subst c'. inv H5.
 eapply composite_consistent_stable. apply SUB1. apply H1; eauto.
 eapply composite_consistent_stable. apply SUB1. apply H1; eauto.
 eapply composite_consistent_stable. apply SUB2. apply H2; eauto.
 inv MERGE.
- (* composite_env_legal_fieldlist *)
 clear - LFce1 LFce2 MERGE.
 intros i c ?; assert  (H1 := LFce1 i c); assert (H2 := LFce2 i c).
 apply (merge_PTrees_e i) in MERGE.
 rewrite get_composite_env_of_QPcomposite_env in H.
 rewrite get_composite_env_of_QPcomposite_env in H1, H2.
 destruct H as [? [? ?]].
 rewrite H in MERGE.
 destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
 destruct MERGE as [c' [? ?]].
 destruct (QPcomposite_eq c0 c1) eqn:?H in H4; inv H4. apply QPcomposite_eq_e in H6; subst c'. inv H5.
 eauto.
 eauto.
 eauto.
 eauto.
- (*composite_env_complete_legal_cosu_type *)
 clear - COSUce1 COSUce2 MERGE SUB1 SUB2.
 intros i c ?; assert  (H1 := COSUce1 i c); assert (H2 := COSUce2 i c).
 apply (merge_PTrees_e i) in MERGE.
 rewrite get_composite_env_of_QPcomposite_env in H.
 rewrite get_composite_env_of_QPcomposite_env in H1, H2.
 destruct H as [? [? ?]].
 rewrite H in MERGE.
 destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
 destruct MERGE as [c' [? ?]].
 destruct (QPcomposite_eq c0 c1) eqn:?H in H4; inv H4. apply QPcomposite_eq_e in H6; subst c'. inv H5.
 eapply complete_legal_cosu_stable. apply SUB1. apply H1; eauto.
 eapply complete_legal_cosu_stable. apply SUB1. apply H1; eauto.
 eapply complete_legal_cosu_stable. apply SUB2. apply H2; eauto.
 inv MERGE.
- (* hardware_alignof_env_consistent *)
 clear - HAce1 HAce2 MERGE HA1 HA2 SUB1 SUB2 CONSce1 CONSce2.
 intros i c ha ? H8; assert  (H1 := HAce1 i c ha); assert (H2 := HAce2 i c ha).
(*   pose proof (co_consistent_complete _ _ CONSce1).*)
 assert ( (composite_env_of_QPcomposite_env _ OKce1) ! i = Some c /\ 
              (PTree.map1 QP.co_ha ce1) ! i = Some ha 
   \/ (composite_env_of_QPcomposite_env _ OKce2) ! i = Some c /\ 
              (PTree.map1 QP.co_ha ce2) ! i = Some ha ). {
   clear - MERGE H H8.
   rewrite !PTree.gmap1 in *. unfold option_map in *.
   apply (merge_PTrees_e i) in MERGE.
   rewrite get_composite_env_of_QPcomposite_env in H.
   rewrite !get_composite_env_of_QPcomposite_env.
   destruct H as [? [? ?]].
   rewrite H in MERGE.
   assert (ce1 ! i = ce ! i \/ ce2 ! i = ce ! i). {
     clear - MERGE H. 
     destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
     destruct MERGE as [c' [? ?]].
     destruct (QPcomposite_eq _ _) eqn:?H in H2; inv H2. apply QPcomposite_eq_e in H4; subst.
     left; congruence. left; congruence. right; congruence. inv MERGE.
   }
   clear MERGE. rewrite H in H8. inv H8.
  destruct H0; rewrite H0, H; [left | right]; split; eauto.
 }
 clear MERGE H8.
 destruct H0 as [[? ?]|[? ?]].
 +
  specialize (H1 H0 H3). clear H3.  subst ha.
  eapply hardware_alignof_composite_stable; eauto.
 +
  specialize (H2 H0 H3). clear H3.  subst ha.
  eapply hardware_alignof_composite_stable; eauto.
- (* legal_alignas_env_consistent *)
(* clear - HAce1 HAce2 MERGE HA1 HA2 LA1 LA2 SUB1 SUB2 CONSce1 CONSce2. *)
  intros i c la ? H8.
 assert ( (composite_env_of_QPcomposite_env _ OKce1) ! i = Some c /\ 
              (PTree.map1 QP.co_la ce1) ! i = Some la 
   \/ (composite_env_of_QPcomposite_env _ OKce2) ! i = Some c /\ 
              (PTree.map1 QP.co_la ce2) ! i = Some la ). {
   clear - MERGE H H8.
   rewrite !PTree.gmap1 in *. unfold option_map in *.
   apply (merge_PTrees_e i) in MERGE.
   rewrite get_composite_env_of_QPcomposite_env in H.
   rewrite !get_composite_env_of_QPcomposite_env.
   destruct H as [? [? ?]].
   rewrite H in MERGE.
   assert (ce1 ! i = ce ! i \/ ce2 ! i = ce ! i). {
     clear - MERGE H. 
     destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
     destruct MERGE as [c' [? ?]].
     destruct (QPcomposite_eq _ _) eqn:?H in H2; inv H2. apply QPcomposite_eq_e in H4; subst.
     left; congruence. left; congruence. right; congruence. inv MERGE.
   }
   clear MERGE. rewrite H in H8. inv H8.
  destruct H0; rewrite H0, H; [left | right]; split; eauto.
 }
 clear MERGE H8.
 destruct H0 as [[? ?]|[? ?]].
 +
   rewrite (LAce1 i c la H0 H1).
   eapply legal_alignas_composite_stable; eassumption.
 +
   rewrite (LAce2 i c la H0 H1).
   eapply legal_alignas_composite_stable; eassumption.
- (* legal_alignas_env_sound *)
 assert (H9:
  forall t ofs, 
  @complete_legal_cosu_type (composite_env_of_QPcomposite_env _ OKce) t = true -> 
   is_aligned (composite_env_of_QPcomposite_env _ OKce) (PTree.map1 QP.co_ha ce) (PTree.map1 QP.co_la ce)
      t ofs = true ->
  @complete_legal_cosu_type (composite_env_of_QPcomposite_env _ OKce1) t = true /\
  is_aligned (composite_env_of_QPcomposite_env _ OKce1) (PTree.map1 QP.co_ha ce1) (PTree.map1 QP.co_la ce1) t ofs = true
 \/ 
@complete_legal_cosu_type (composite_env_of_QPcomposite_env _ OKce2) t = true /\
  is_aligned (composite_env_of_QPcomposite_env _ OKce2) (PTree.map1 QP.co_ha ce2) (PTree.map1 QP.co_la ce2) t ofs = true). {
 induction t; simpl; intros; auto.
 - 
    specialize (IHt ofs H).
    spec IHt. clear - H0. 
    unfold is_aligned in H0|-*; simpl in H0.
    unfold is_aligned_aux in *.
    InvBooleans; auto. rewrite andb_true_iff; split; auto.
    destruct IHt as [[? ?]|[? ?]]; [left|right]; split; auto;
    unfold is_aligned in *; simpl in *; unfold is_aligned_aux in *;
    InvBooleans; simpl in *; rewrite ?andb_true_iff; split; auto; split; auto.
  +
    rewrite (sizeof_type_stable' _ _ t SUB1 H1).
    rewrite (hardware_alignof_type_stable' _ _ SUB1 _ _ HA1); auto.
    apply samedom_ha_composite_env_of_QPcomposite_env.
    apply complete_legal_cosu_type_complete_type; auto.
  +
    rewrite (sizeof_type_stable' _ _ t SUB2 H1).
    rewrite (hardware_alignof_type_stable' _ _ SUB2 _ _ HA2); auto.
    apply samedom_ha_composite_env_of_QPcomposite_env.
    apply complete_legal_cosu_type_complete_type; auto.
 -
   destruct ((composite_env_of_QPcomposite_env ce OKce) ! i) eqn:?H; try discriminate H.
   destruct (co_su c) eqn:?H; try discriminate H.
   rename H into PLAIN.
 assert ( (composite_env_of_QPcomposite_env _ OKce1) ! i = Some c
   \/ (composite_env_of_QPcomposite_env _ OKce2) ! i = Some c ). {
   clear - MERGE H1.
   apply (merge_PTrees_e i) in MERGE.
   rewrite get_composite_env_of_QPcomposite_env in H1.
   rewrite !get_composite_env_of_QPcomposite_env.
   destruct H1 as [? [? ?]].
   rewrite H in MERGE.
   assert (ce1 ! i = ce ! i \/ ce2 ! i = ce ! i). {
     clear - MERGE H. 
     destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
     destruct MERGE as [c' [? ?]].
     destruct (QPcomposite_eq _ _) eqn:?H in H2; inv H2. apply QPcomposite_eq_e in H4; subst.
     left; congruence. left; congruence. right; congruence. inv MERGE.
   }
   clear MERGE. rewrite H in H0.
  destruct H0; [left|right]; exists x, x0; rewrite H0; auto.
 }
  destruct H; [left|right]; rewrite H, H2; split; auto.
 +
   unfold is_aligned in *; simpl in *; unfold is_aligned_aux in *.
   rewrite get_composite_env_of_QPcomposite_env in *.
   destruct H1 as [ha [la ?]]. destruct H as [ha' [la' ?]].
   pose proof (HA1 i ha'). pose proof (LA1 i la').
   rewrite !PTree.gmap1 in H0. 
   rewrite !PTree.gmap1 in H3. 
   rewrite !PTree.gmap1 in H4. 
   rewrite !PTree.gmap1.
   unfold option_map in *. rewrite H in *.  
   specialize (H3 (eq_refl _)).
   specialize (H4 (eq_refl _)).   
    simpl QP.co_ha in *; simpl QP.co_la  in *.
   destruct  (ce ! i) eqn:?H; inv H3. inv H4. inv H1. simpl in H.  auto.
 +
   unfold is_aligned in *; simpl in *; unfold is_aligned_aux in *.
   rewrite get_composite_env_of_QPcomposite_env in *.
   destruct H1 as [ha [la ?]]. destruct H as [ha' [la' ?]].
   pose proof (HA2 i ha'). pose proof (LA2 i la').
   rewrite !PTree.gmap1 in H0. 
   rewrite !PTree.gmap1 in H3. 
   rewrite !PTree.gmap1 in H4. 
   rewrite !PTree.gmap1.
   unfold option_map in *. rewrite H in *.  
   specialize (H3 (eq_refl _)).
   specialize (H4 (eq_refl _)).
    simpl.
   destruct  (ce ! i) eqn:?H; inv H3. inv H4. inv H1. simpl in H.  auto.
 -
 destruct ((composite_env_of_QPcomposite_env ce OKce) ! i) eqn:?H; inv H.
 destruct (co_su c) eqn:?H; try discriminate.
 assert ( (composite_env_of_QPcomposite_env _ OKce1) ! i = Some c
   \/ (composite_env_of_QPcomposite_env _ OKce2) ! i = Some c ). {
   clear - MERGE H1.
   apply (merge_PTrees_e i) in MERGE.
   rewrite get_composite_env_of_QPcomposite_env in H1.
   rewrite !get_composite_env_of_QPcomposite_env.
   destruct H1 as [? [? ?]].
   rewrite H in MERGE.
   assert (ce1 ! i = ce ! i \/ ce2 ! i = ce ! i). {
     clear - MERGE H. 
     destruct (ce1 ! i) eqn:?H; destruct (ce2 ! i) eqn:?H.
     destruct MERGE as [c' [? ?]].
     destruct (QPcomposite_eq _ _) eqn:?H in H2; inv H2. apply QPcomposite_eq_e in H4; subst.
     left; congruence. left; congruence. right; congruence. inv MERGE.
   }
   clear MERGE. rewrite H in H0.
  destruct H0; [left|right]; exists x, x0; rewrite H0; auto.
 }
  destruct H2; [left|right]; rewrite H2,H; split; auto.
 +
   unfold is_aligned in *; simpl in *; unfold is_aligned_aux in *.
   rewrite get_composite_env_of_QPcomposite_env in *.
   destruct H1 as [ha [la ?]]. destruct H2 as [ha' [la' ?]].
   pose proof (HA1 i ha'). pose proof (LA1 i la').
   rewrite !PTree.gmap1 in H0. 
   rewrite !PTree.gmap1 in H4. 
   rewrite !PTree.gmap1 in H5. 
   rewrite !PTree.gmap1.
   unfold option_map in *. rewrite H1,H2 in *.
   specialize (H4 (eq_refl _)).
   specialize (H5 (eq_refl _)).
    simpl. inv H4; inv H5. simpl in H0. rewrite H3. auto.
 +
   unfold is_aligned in *; simpl in *; unfold is_aligned_aux in *.
   rewrite get_composite_env_of_QPcomposite_env in *.
   destruct H1 as [ha [la ?]]. destruct H2 as [ha' [la' ?]].
   pose proof (HA2 i ha'). pose proof (LA2 i la').
   rewrite !PTree.gmap1 in H0. 
   rewrite !PTree.gmap1 in H4. 
   rewrite !PTree.gmap1 in H5. 
   rewrite !PTree.gmap1.
   unfold option_map in *. rewrite H1,H2 in *.
   specialize (H4 (eq_refl _)).
   specialize (H5 (eq_refl _)).
    simpl. inv H4; inv H5. simpl in H0. rewrite H3; auto.
 }
  hnf; intros.
  destruct (H9 _ _ H H0) as [[??]|[??]]; clear H9.
 +
  pose proof (LASce1 _ _ H1 H2).
  eapply align_compatible_rec_stable'; try apply H3; auto.
 +
  pose proof (LASce2 _ _ H1 H2).
  eapply align_compatible_rec_stable'; try apply H3; auto.
Qed.

Lemma tree'_not_empty':
  forall {A} (m: PTree.tree' A),
   exists i, isSome (PTree.get' i m) = True.
Proof.
intros.
destruct (PTree.tree'_not_empty m) as [i ?].
exists i.
destruct (PTree.get' i m). reflexivity. congruence.
Qed. 

Lemma PTree_samedom_i {A} {B} (m1: PTree.t A) (m2: PTree.t B):
 (forall i, isSome (m1 ! i) = isSome (m2 ! i)) ->
 PTree_samedom m1 m2.
Proof.
destruct m1 as [|m1], m2 as [|m2]; simpl; intros; auto; unfold PTree.get in H.
destruct (tree'_not_empty' m2) as [i ?]. specialize (H i). rewrite H, H0; auto.
destruct (tree'_not_empty' m1) as [i ?]. specialize (H i). rewrite <- H, H0; auto.
revert m2 H; induction m1; destruct m2; simpl; intros;
try solve [apply IHm1; intro i; apply (H (xI i))];
try solve [specialize (H xH); simpl in H; rewrite ?H; auto; rewrite <- H; auto].
destruct (tree'_not_empty' m1) as [i H0].
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m2_1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m2) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m2) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m2_1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m2_1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
apply IHm1. intro i; apply (H (xO i)).
destruct (tree'_not_empty' m2_2) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1_1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1_2) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
split.
apply IHm1_1; intro i; apply (H (xO i)).
apply IHm1_2; intro i; apply (H (xI i)).
destruct (tree'_not_empty' m1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
apply IHm1. intro i; apply (H (xO i)).
destruct (tree'_not_empty' m2_2) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1_2) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1_1) as [i H0];
 specialize (H (xO i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
destruct (tree'_not_empty' m1_2) as [i H0];
 specialize (H (xI i)); simpl in H; rewrite H0 in H; simpl in H;
 rewrite ?H; auto; rewrite <- H; auto.
split.
apply IHm1_1; intro i; apply (H (xO i)).
apply IHm1_2; intro i; apply (H (xI i)).
Qed.

Lemma PTree_samedom_ha: forall cs, PTree_samedom (@cenv_cs cs) (@ha_env_cs cs).
Proof.
  intro cs.
  apply PTree_samedom_i. intro i.
  pose proof (@ha_env_cs_complete cs i).
  destruct (cenv_cs ! i), (ha_env_cs ! i); auto.
  destruct H as [[? ?] _]; eauto. inv H.
  destruct H as [_ [? ?]]; eauto. inv H.
Qed.

Lemma PTree_samedom_la: forall cs, PTree_samedom (@cenv_cs cs) (@la_env_cs cs).
Proof.
  intro cs.
  apply PTree_samedom_i. intro i.
  pose proof (@la_env_cs_complete cs i).
  destruct (cenv_cs ! i), (la_env_cs ! i); auto.
  destruct H as [[? ?] _]; eauto. inv H.
  destruct H as [_ [? ?]]; eauto. inv H.
Qed.

Lemma QPcompspecs_OK_i:
 forall {cs: compspecs}, 
 @PTree_samedom composite Z (@cenv_cs cs) (@ha_env_cs cs) ->
 @PTree_samedom composite legal_alignas_obs (@cenv_cs cs) (@la_env_cs cs) ->
 QPcompspecs_OK
    (QPcomposite_env_of_composite_env (@cenv_cs cs) (@ha_env_cs cs) (@la_env_cs cs)).
Proof.
intros cs H1 H2.
assert (QPcomposite_env_OK (QPcomposite_env_of_composite_env (@cenv_cs cs) (@ha_env_cs cs) (@la_env_cs cs))) .
apply QPcomposite_env_of_composite_env_OK; auto;
  apply PTree_samedom_domain_eq; auto.
exists H.
rewrite composite_env_of_QPcomposite_env_of_composite_env; auto.
intros ce'.
subst ce'.
cbv delta [QPcomposite_env_of_composite_env].
rewrite PTree_map1_map3 with (e:=0);
 [ | apply PTree_samedom_ha | apply PTree_samedom_la].
rewrite PTree_map1_map3 with (e:=false);
 [ | apply PTree_samedom_ha | apply PTree_samedom_la].
replace (fun (x1 : composite) (x2 : Z) (x3 : legal_alignas_obs) =>
     QP.co_ha (QPcomposite_of_composite x1 x2 x3))
 with (fun  (x1 : composite) (x2 : Z) (x3 : legal_alignas_obs)  => x2)
  by (extensionality x1 x2 x3; reflexivity).
replace (fun (x1 : composite) (x2 : Z) (x3 : legal_alignas_obs) =>
     QP.co_la (QPcomposite_of_composite x1 x2 x3))
 with (fun  (x1 : composite) (x2 : Z) (x3 : legal_alignas_obs)  => x3)
  by (extensionality x1 x2 x3; reflexivity).
rewrite PTree_map3_2 by auto. 
rewrite PTree_map3_3 by auto.
simpl.
split3; [ | | split3; [ | | split]]; try apply cs.
Qed.
 
Definition cspecs_eq cs1 cs2 := cspecs_sub cs1 cs2 /\ cspecs_sub cs2 cs1.

Lemma QPcompspecs_OK_e:
 forall ce
  (H: QPcompspecs_OK ce),
 let cs := compspecs_of_QPcomposite_env _ H in
    @cenv_cs cs = (composite_env_of_QPcomposite_env ce (projT1 H))
  /\ @ha_env_cs cs = PTree.map1 QP.co_ha ce 
  /\ @la_env_cs cs = PTree.map1 QP.co_la ce.
Proof.
intros.
destruct H.
simpl.
set (ce' := composite_env_of_QPcomposite_env ce x) in *.
set (ha' :=  PTree.map1 QP.co_ha ce) in *.
set (la' := PTree.map1 QP.co_la ce) in *.
destruct a as [? [? [? [? [? ?]]]]].
pose proof (hardware_alignof_env_completeQP _ x).
pose proof (legal_alignas_env_completeQP _ x).
simpl.
split3; auto.
Qed. 

Lemma cspecs_sub_of_QPsub:
 forall ce1 ce2 (OK1: QPcompspecs_OK ce1) (OK2: QPcompspecs_OK ce2),
  PTree_sub ce1 ce2 ->
  cspecs_sub  (compspecs_of_QPcomposite_env _ OK1) 
             (compspecs_of_QPcomposite_env _ OK2).
Proof.
intros.
destruct (QPcompspecs_OK_e _ OK1) as [?H [?H ?H]].
destruct (QPcompspecs_OK_e _ OK2) as [?H [?H ?H]].
simpl in *.
split3; intros ?; specialize (H i); unfold sub_option, tycontext.sub_option in *.
rewrite H0, H3.
destruct ( (composite_env_of_QPcomposite_env ce1 (projT1 OK1)) ! i) eqn:?H; auto.
rewrite get_composite_env_of_QPcomposite_env in H6|-*.
destruct H6 as [ha [la ?]]; exists ha, la.
rewrite H6 in H. auto.
rewrite H1, H4.
rewrite !PTree.gmap1.
unfold option_map.
destruct (ce1 ! i) eqn:?H; auto. rewrite H; auto.
rewrite H2, H5.
rewrite !PTree.gmap1.
unfold option_map.
destruct (ce1 ! i) eqn:?H; auto. rewrite H; auto.
Qed.

Fixpoint put_at_nth (i: nat) (c: ident * QP.composite) (rl: list (list (ident * QP.composite))) : list (list (ident * QP.composite)) :=
 match i, rl with
 | O, r::rl' =>  (c::r)::rl'
 | S j, r::rl' => r :: put_at_nth j c rl'
 | O, nil => (c::nil)::nil
 | S j, nil => nil :: put_at_nth j c nil
 end.

Fixpoint sort_rank (al: list (ident * QP.composite)) (rl: list (list (ident * QP.composite))) : list (ident * QP.composite) :=
  match al with
  | nil => List.fold_right (@app (ident * QP.composite)) nil rl
  | c::cl => sort_rank cl (put_at_nth (QP.co_rank (snd c)) c rl)
 end.

Definition compdef_of_compenv_element (x: ident * QP.composite) : composite_definition :=
  Composite (fst x) (QP.co_su (snd x)) (QP.co_members (snd x)) (QP.co_attr (snd x)).

Import ListNotations.

Definition cenv_built_correctly_each 
     (cd: composite_definition) (tr: Errors.res composite_env)  :=
                Errors.bind tr (fun ce' => 
                match cd with Composite i su mems att =>
                 match PTree.get i ce' with 
                 | None => Errors.Error [Errors.MSG "Composite identifier duplicate or not found in composite_env:";
                                                       Errors.POS i]
                 | Some c =>
                             let d := PTree.remove i ce' in
                             let m := c.(co_members) in 
                             if (eqb_su su c.(co_su)
                             && eqb_list eqb_member mems m
                             && eqb_attr att c.(co_attr)
                             && complete_members d m
                             && Z.eqb (align (sizeof_composite d c.(co_su) m) c.(co_alignof)) c.(co_sizeof)
                             && Z.eqb (align_attr att (alignof_composite d m)) c.(co_alignof)
                             && Nat.eqb (rank_members d m) c.(co_rank)
                              )%bool
                              then Errors.OK (PTree.remove i ce')
                              else Errors.Error [Errors.MSG "Composite definition does not match:";
                                                          Errors.POS i]
                end end).

Definition cenv_built_correctly_finish (ce': composite_env) :=
   let leftovers := PTree.elements ce' in
   if Nat.eqb (List.length leftovers) O
   then Errors.OK tt
   else Errors.Error (Errors.MSG "Composite_env contains extra identifiers:" ::
                   map Errors.POS (map fst leftovers)).

Definition cenv_built_correctly
   (comps: list composite_definition)
   (ce: composite_env) : Errors.res unit := 
  Errors.bind (fold_right cenv_built_correctly_each (Errors.OK ce) comps)
   cenv_built_correctly_finish.

Lemma cenv_built_correctly_e:
  forall (comps : list composite_definition)
           (ce : composite_env),
  cenv_built_correctly comps ce = Errors.OK tt ->
  build_composite_env comps = Errors.OK ce.
Proof.
intros. 
unfold build_composite_env.
unfold cenv_built_correctly in H.
unfold Errors.bind in H.
destruct (fold_right cenv_built_correctly_each (Errors.OK ce) comps) eqn:?H; [ | discriminate].
unfold cenv_built_correctly_finish in H.
destruct (PTree.elements c) eqn:?H; [ | inv H].
clear H.
assert (c = PTree.empty _). {
 apply PTree.extensionality.
 intro i. destruct (c ! i) eqn:?H; auto.
  apply PTree.elements_correct in H. rewrite H1 in H; inv H.
}
subst c. clear H1.
forget (PTree.empty composite) as d.
rename H0 into H.
rename d into c.
revert ce c H.
forget (PTree.empty composite) as d.
induction comps; simpl; intros.
auto.
destruct a.
destruct (fold_right cenv_built_correctly_each (Errors.OK ce) comps) eqn:?H;
  try discriminate.
simpl in H.
destruct (c0 ! id) eqn:?H; try discriminate.
match type of H with ((if ?A then _ else _) = _) =>
  destruct A eqn:?H;  [ | discriminate H]
end.
InvBooleans.
apply eqb_su_spec in H2.
apply eqb_list_spec in H9; [ | apply eqb_member_spec].
apply eqb_attr_spec in H8.
apply Nat.eqb_eq in H4.
apply Z.eqb_eq in H5.
apply Z.eqb_eq in H6.
subst.
inv H.
unfold Errors.bind.
clear d. rename c0 into d.
rewrite composite_of_def_eq; auto.
replace  (PTree.set id c1 (PTree.remove id d)) with d.
auto.
apply PTree.extensionality.
intro i. destruct (ident_eq i id). subst. rewrite PTree.gss. auto. rewrite PTree.gso by auto. rewrite PTree.gro by auto; auto.
constructor; auto.
rewrite PTree.grs.
auto.
Qed.

Lemma samedom_composite_env_of_QPcomposite_env:
 forall ce H, PTree_samedom (composite_env_of_QPcomposite_env ce H) ce.
Proof.
destruct ce as [|ce]; simpl; auto. 
induction ce; simpl; intros; auto.
Qed.

(*
Lemma rebuild_composite_env:
  forall (ce: QP.composite_env) (OK: QPcomposite_env_OK ce),
 build_composite_env
    (map compdef_of_compenv_element (sort_rank (PTree.elements ce) nil)) =
  Errors.OK (composite_env_of_QPcomposite_env ce OK).
Proof.
intros.
apply cenv_built_correctly_e.

apply test_PTree_canonical_e in CAN.
unfold build_composite_env.
assert (CAN' := @PTree_canonical_empty composite).
pose proof (proj1 (PTree_Forall_elements _ _ _) OK).



Admitted.  (* Probably true *)
*)


