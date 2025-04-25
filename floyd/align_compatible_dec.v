Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.fieldlist.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Open Scope Z.

Module Type ACR_DEC.

  Parameter align_compatible_rec_dec:
    forall {cs: compspecs},
      forall t z, {align_compatible_rec cenv_cs t z} + {~ align_compatible_rec cenv_cs t z}.

End ACR_DEC.

Module align_compatible_rec_dec: ACR_DEC.

Section align_compatible_rec_dec.

Context {cs: compspecs}.

Definition dec_type := sigT (fun P: Z -> Prop => forall z: Z, {P z} + {~ P z} ).

Definition dec_by_value (ch: memory_chunk): dec_type :=
  existT (P := fun P: Z -> Prop => forall z: Z, {P z} + {~ P z} ) 
   (fun z => (Memdata.align_chunk ch | z))
   (fun z => Zdivide_dec (Memdata.align_chunk ch) z (*Memdata.align_chunk_pos _*)).

Definition dec_False: dec_type :=
  existT (P := fun P: Z -> Prop => forall z: Z, {P z} + {~ P z} ) (fun z => False%type) (fun z => right (fun H => H)).

Definition dec_True: dec_type :=
  existT (P := fun P: Z -> Prop => forall z: Z, {P z} + {~ P z} ) (fun z => True%type) (fun z => left I).

Fixpoint cons_in_list {A} (a: A) (al' al: list A) (H: forall x, In x al' -> In x al) (bl: list {x:A| In x al'} ) : list {x: A | In x al} :=
  match bl with
  | nil => nil
  | exist x i :: bl0 =>exist _ x (H x i)  :: cons_in_list a al' al H bl0
  end.

Fixpoint make_in_list {A} (al: list A) : list {x: A | In x al} := 
  match al as ax return (al = ax -> list {x : A | In x ax} ) with
           | nil => fun _ => nil
           | a::al' => fun H: al = a::al' =>
                      exist _ a (or_introl eq_refl) ::
                         eq_rect al (fun l : list A => list {x : A | In x l} )
                          (cons_in_list a al' al (fun (x : A) (H0 : In x al') =>
                                 eq_ind_r (fun al0 : list A => In x al0) (in_cons _ _ _ H0) H)
                               (make_in_list al'))
                        (a :: al') H
           end (eq_refl _).

Lemma in_make_in_list: forall {A} (a: A) (al: list A) H,
   In (exist (fun x => In x al) a H) (make_in_list al).
Proof.
induction al; intros.
inv H.
destruct H.
subst a0.
simpl.
left; auto.
unfold make_in_list; fold @make_in_list.
right.
specialize (IHal i).
unfold eq_rect.
forget (make_in_list al) as bl.
unfold eq_ind_r.
unfold eq_ind.
simpl.
induction bl.
inv IHal.
destruct IHal.
subst a1.
left. 
apply exist_ext; auto.
specialize (IHbl H).
unfold cons_in_list; fold @cons_in_list.
destruct a1.
right. auto.
Qed.

Lemma field_type_in_members_strong:
 forall i t m
  (PLAIN: plain_members m = true),
   Ctypes.field_type i m = Errors.OK t ->
          In (Member_plain i t) m.
Proof.
induction m as [|[|]]; intros.
inv H.
simpl in H.
if_tac in H. subst. inv H. left; auto.
right. apply IHm; auto.
inv PLAIN.
Qed.

Lemma align_compatible_dec_aux:
   forall n t, (rank_type cenv_cs t < n)%nat ->
    forall z, {align_compatible_rec cenv_cs t z} + {~ align_compatible_rec cenv_cs t z}.
Proof.
induction n; intros; [ lia | ].
rename H into Hrank.
destruct t  as [ | [ | | | ] [ | ]| [ | ] | [ | ] | | | | | ] eqn:Ht; intros;
try solve [
clear IHn Hrank;
match goal with |- context [align_compatible_rec _ ?t _] =>
evar (ch: memory_chunk);
assert (access_mode t = By_value ch) by (subst ch; reflexivity);
(destruct (Zdivide_dec (Memdata.align_chunk ch) z);
   [left; econstructor; try reflexivity; eassumption
   |right;  contradict n; inv n; inv H0; auto])
end];
try solve [right; intro H; inv H; inv H0].
* (* Tarray *)
specialize (IHn t0).
simpl in Hrank. spec IHn; [lia | ]. clear Hrank.
pose proof (Zrange_pred_dec (fun ofs => align_compatible_rec cenv_cs t0 (z + sizeof t0 * ofs))).
spec H.
intro; apply IHn.
specialize (H 0 z0).
destruct H as [H|H]; [left|right].
+
eapply align_compatible_rec_Tarray; intros.
apply H; auto.
+
contradict H.
intros.
eapply align_compatible_rec_Tarray_inv in H.
apply H.
split; try lia.
* (* Tstruct *)
destruct (cenv_cs !! i) eqn:?H;
 [ | right; intro H0; inv H0].
destruct (plain_members (co_members c)) eqn:?PLAIN;
   [ | right; intro Hx; inv Hx; congruence].
simpl in Hrank. rewrite H in Hrank.
pose (FO id := match Ctypes.field_offset cenv_cs id (co_members c) with
                      | Errors.OK (z0, Full) => z0 | _ => 0 end).
pose (D := fun x: {it: member | In it (co_members c)} =>
                align_compatible_rec cenv_cs (type_member (proj1_sig x)) (z + FO (name_member (proj1_sig x)))).
assert (H1: forall x, {D x} + {~ D x} ). {
 subst D. intros. destruct x as [[id t0|] ?].
2:{ exfalso. clear - i0 PLAIN. 
   induction (co_members c) as [|[|]]; simpl in *; try discriminate; auto. destruct i0; auto. discriminate.
 }
 simpl.
 apply IHn.
 assert (H1:= rank_union_member cenv_cs _ a _ _ cenv_consistent H i0).
 simpl in H1. rewrite H in H1. lia.
}
destruct (Forall_dec D H1 (make_in_list (co_members c))) as [H2|H2]; clear H1; [left|right].
+
 eapply align_compatible_rec_Tstruct.
 eassumption. auto.
 assert (H1 := proj1 (Forall_forall _ _) H2); clear H2.
 intros.
 specialize (H1 (exist _ (Member_plain i0 t0) (field_type_in_members_strong _ _ _ PLAIN H0))).
 specialize (H1 (in_make_in_list _ _ _)).
 subst D.
 simpl in H1.
 replace z0 with (FO i0).
 apply H1.
 unfold FO. rewrite H2. auto.
+
 contradict H2.
 apply Forall_forall.
 intros.
 subst D. simpl.
 destruct x as [[id t0|] ?].
2:{ exfalso. clear - i0 PLAIN. 
   induction (co_members c) as [|[|]]; simpl in *; try discriminate; auto. destruct i0; auto. discriminate.
 }
 eapply align_compatible_rec_Tstruct_inv in H2; try eassumption.
 instantiate (1:=id). simpl.
 pose proof (get_co_members_no_replicate i).
 unfold get_co in H1. rewrite H in H1. unfold members_no_replicate in H1.
 clear - i0 H1 PLAIN.
 induction (co_members c) as [|[|]]; [ | | discriminate]. inv i0. simpl.
 if_tac. subst. 
 simpl in H1. destruct (id_in_list id0 (map name_member m)) eqn:?; try discriminate.
 destruct i0. inv H. auto.
 apply id_in_list_false in Heqb.
 exfalso. apply Heqb. apply (in_map name_member) in H. apply H.
 apply IHm. auto.
 destruct i0. inv H0. auto.
 simpl in H1. destruct (id_in_list id0 (map name_member m)) eqn:?; try discriminate.
 auto.
 unfold FO; simpl.
 clear - i0 PLAIN.
 assert (in_members id (co_members c)). unfold in_members. apply (in_map name_member) in i0; auto.
 pose proof (plain_members_field_offset _ PLAIN _ _ H). rewrite H0. auto.
* (* Tunion *)
destruct (cenv_cs !! i) eqn:?H;
 [ | right; intro H0; inv H0; congruence].
destruct (plain_members (co_members c)) eqn:?PLAIN;
   [ | right; intro Hx; inv Hx; congruence].
simpl in Hrank. rewrite H in Hrank.
pose (D := fun x: {it: member | In it (co_members c)} =>
                align_compatible_rec cenv_cs (type_member (proj1_sig x)) z).
assert (H1: forall x, {D x} + {~ D x} ). {
 subst D. intros. destruct x as [[id t0|] ?].
2:{ exfalso. clear - i0 PLAIN. 
   induction (co_members c) as [|[|]]; simpl in *; try discriminate; auto. destruct i0; auto. discriminate.
 }
 simpl.
 apply IHn.
 assert (H1:= rank_union_member cenv_cs _ a _ _ cenv_consistent H i0).
 simpl in H1. rewrite H in H1. lia.
}
destruct (Forall_dec D H1 (make_in_list (co_members c))) as [H2|H2]; clear H1; [left|right].
+
 eapply align_compatible_rec_Tunion.
 eassumption. auto.
 assert (H1 := proj1 (Forall_forall _ _) H2); clear H2.
 intros.
 specialize (H1 (exist _ (Member_plain i0 t0) (field_type_in_members_strong _ _ _ PLAIN H0))).
 specialize (H1 (in_make_in_list _ _ _)).
 apply H1.
+
 contradict H2.
 apply Forall_forall.
 intros.
 subst D. simpl.
 destruct x as [[id t0|] ?].
2:{ exfalso. clear - i0 PLAIN. 
   induction (co_members c) as [|[|]]; simpl in *; try discriminate; auto. destruct i0; auto. discriminate.
 }
 eapply align_compatible_rec_Tunion_inv in H2; try eassumption.
 instantiate (1:=id). simpl.
 pose proof (get_co_members_no_replicate i).
 unfold get_co in H1. rewrite H in H1. unfold members_no_replicate in H1.
 clear - i0 H1 PLAIN.
 induction (co_members c) as [|[|]]; [ | | discriminate]. inv i0. simpl.
 if_tac. subst.
 simpl in H1. destruct (id_in_list id0 (map name_member m)) eqn:?; try discriminate.
 destruct i0. inv H. auto.
 apply id_in_list_false in Heqb.
 exfalso. apply Heqb. apply (in_map name_member) in H. apply H.
 apply IHm; auto.  
 destruct i0. inv H0. auto.
 simpl in H1. destruct (id_in_list id0 (map name_member m)) eqn:?; try discriminate.
 auto.
Qed.

Lemma align_compatible_rec_dec: forall t z, {align_compatible_rec cenv_cs t z} + {~ align_compatible_rec cenv_cs t z}.
Proof.
intros.
apply align_compatible_dec_aux with (S (rank_type cenv_cs t)).
lia.
Qed.

End align_compatible_rec_dec.

End align_compatible_rec_dec.

Lemma align_compatible_dec: forall {cs: compspecs} t p, {align_compatible t p} + {~ align_compatible t p}.
Proof.
  intros.
  destruct p; try solve [left; unfold align_compatible; simpl; tauto].
  simpl.
  apply align_compatible_rec_dec.align_compatible_rec_dec.
Qed.
