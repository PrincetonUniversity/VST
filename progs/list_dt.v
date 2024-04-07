(* Require Import VST.floyd.proofauto.
   TEMPORARILY replace "floyd.proofauto"
   with all the imports in the list below.
   This reduces makefile-based recompilation
   when changing things in (e.g.) forward.v
*)
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_loadstore.
(*Require Import VST.floyd.unfold_data_at.*)
Require Import VST.floyd.entailer.
Require Import VST.floyd.compat.
(*  End TEMPORARILY *)

Lemma int64_eq_e: forall i j, Int64.eq i j = true -> i=j.
Proof. intros. pose proof (Int64.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma ptrofs_eq_e: forall i j, Ptrofs.eq i j = true -> i=j.
Proof. intros. pose proof (Ptrofs.eq_spec i j); rewrite H in H0; auto. Qed.

Class listspec {cs: compspecs} (list_structid: ident) (list_link: ident) (token: share -> val -> mpred):=
  mk_listspec {
   list_fields: members;
   list_struct := Tstruct list_structid noattr;
   list_members_eq: list_fields = co_members (get_co list_structid);
   list_struct_complete_legal_cosu: complete_legal_cosu_type list_struct = true; (* TODO: maybe this line not useful? *)
   list_link_type: nested_field_type list_struct (StructField list_link :: nil) = Tpointer list_struct noattr;
   list_token := token;
   list_plain: plain_members list_fields = true
}.

Section LIST1.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident} {list_token: share -> val -> mpred}.

Fixpoint all_but_link (f: members) : members :=
 match f with
 | nil => nil
 | cons it f' => if ident_eq (name_member it) list_link
                               then f'
                               else cons it (all_but_link f')
 end.

Lemma list_link_size_in_range (ls: listspec list_structid list_link list_token):
  0 < sizeof (nested_field_type list_struct (StructField list_link :: nil)) < Ptrofs.modulus.
Proof.
  rewrite list_link_type.
  unfold sizeof, Ctypes.sizeof.
  destruct Archi.ptr64 eqn:Hp.
  rewrite Ptrofs.modulus_eq64 by auto; computable.
  rewrite Ptrofs.modulus_eq32 by auto; computable.
Qed.

Definition elemtype (ls: listspec list_structid list_link list_token) :=
  compact_prod
  (map (fun it => reptype (field_type (name_member it) list_fields)) (all_but_link list_fields)).

Definition field_type'  (F: members) (it: member) :=
   reptype (field_type (name_member it) F).

Definition add_link_back' {F f: members}
  (v: compact_prod (map (field_type' F) (all_but_link f))) :
  compact_prod (map (field_type' F) f).
  induction f as [| it0 f].
  + exact tt.
  +  destruct f as [| it1 f0].
    - exact (default_val _).
    - change (all_but_link (it0 :: it1 :: f0))
       with (if ident_eq (name_member it0) list_link
                               then it1::f0
                               else cons it0 (all_but_link (it1::f0)))
       in v.
       change (reptype (field_type (name_member it0) F) * compact_prod (map (field_type' F) (it1::f0)))%type.
       destruct (ident_eq (name_member it0) list_link).
       exact (default_val _, v).
       destruct (all_but_link (it1 :: f0)) eqn:?.
       simpl in Heqm.
       destruct (ident_eq (name_member it1) list_link); [ | discriminate Heqm].
        subst f0.
        exact (v, default_val _).
        exact (fst v, IHf (snd v)).
Defined.

Definition add_link_back
 (F f : members)
  (v : compact_prod
         (map (fun it : member => reptype (field_type (name_member it) F))
            (all_but_link f)))
  : compact_prod (map (fun it => reptype (field_type (name_member it) F)) f)
  :=
list_rect
  (fun f0 : list (member) =>
   compact_prod (map (field_type' F) (all_but_link f0)) ->
   compact_prod (map (field_type' F) f0))
  (fun _ : compact_prod (map (field_type' F) (all_but_link nil)) => tt)
  (fun (it0 : member) (f0 : list member)
     (IHf : compact_prod (map (field_type' F) (all_but_link f0)) ->
            compact_prod (map (field_type' F) f0))
     (v0 : compact_prod (map (field_type' F) (all_but_link (it0 :: f0)))) =>
   match
     f0 as l
     return
       (compact_prod (map (field_type' F) (all_but_link (it0 :: l))) ->
        (compact_prod (map (field_type' F) (all_but_link l)) ->
         compact_prod (map (field_type' F) l)) ->
        compact_prod (map (field_type' F) (it0 :: l)))
   with
   | nil =>
       fun
         (_ : compact_prod (map (field_type' F) (all_but_link (it0 :: nil))))
         (_ : compact_prod (map (field_type' F) (all_but_link nil)) ->
              compact_prod (map (field_type' F) nil)) =>
       default_val (field_type (name_member it0) F)
   | it1 :: f1 =>
       fun
         (v1 : compact_prod
                 (map (field_type' F) (all_but_link (it0 :: it1 :: f1))))
         (IHf0 : compact_prod
                   (map (field_type' F) (all_but_link (it1 :: f1))) ->
                 compact_prod (map (field_type' F) (it1 :: f1))) =>
       (if ident_eq (name_member it0) list_link as s0
         return
           (compact_prod
              (map (field_type' F)
                 (if s0 then it1 :: f1 else it0 :: all_but_link (it1 :: f1))) ->
            reptype (field_type (name_member it0) F) *
            compact_prod (map (field_type' F) (it1 :: f1)))
        then
         fun v2 : compact_prod (map (field_type' F) (it1 :: f1)) =>
         (default_val (field_type (name_member it0) F), v2)
        else
         fun
           v2 : compact_prod
                  (map (field_type' F) (it0 :: all_but_link (it1 :: f1))) =>
         match
           all_but_link (it1 :: f1) as l
           return
             (all_but_link (it1 :: f1) = l ->
              compact_prod (map (field_type' F) (it0 :: l)) ->
              (compact_prod (map (field_type' F) l) ->
               compact_prod (map (field_type' F) (it1 :: f1))) ->
              reptype (field_type (name_member it0) F) *
              compact_prod (map (field_type' F) (it1 :: f1)))
         with
         | nil =>
             fun (Heqm0 : all_but_link (it1 :: f1) = nil)
               (v3 : compact_prod (map (field_type' F) (it0 :: nil)))
               (IHf1 : compact_prod (map (field_type' F) nil) ->
                       compact_prod (map (field_type' F) (it1 :: f1))) =>
             let s0 := ident_eq (name_member it1) list_link in
             (if s0
               return
                 ((if s0 then f1 else it1 :: all_but_link f1) = nil ->
                  reptype (field_type (name_member it0) F) *
                  compact_prod (map (field_type' F) (it1 :: f1)))
              then
               fun Heqm1 : f1 = nil =>
               eq_rect_r
                 (fun f2 : members =>
                  (compact_prod (map (field_type' F) nil) ->
                   compact_prod (map (field_type' F) (it1 :: f2))) ->
                  reptype (field_type (name_member it0) F) *
                  compact_prod (map (field_type' F) (it1 :: f2)))
                 (fun
                    _ : compact_prod (map (field_type' F) nil) ->
                        compact_prod (map (field_type' F) (it1 :: nil)) =>
                  (v3, default_val (field_type (name_member it1) F)))
                 Heqm1 IHf1
              else
               fun Heqm1 : it1 :: all_but_link f1 = nil =>
                 False_rect
                   (reptype (field_type (name_member it0) F) *
                    compact_prod (map (field_type' F) (it1 :: f1)))
                 (eq_rect (it1 :: all_but_link f1)
                    (fun e : members =>
                     match e with
                     | nil => False%type
                     | _ :: _ => True%type
                     end) I nil Heqm1)) Heqm0
         | p :: m0 =>
             fun (_ : all_but_link (it1 :: f1) = p :: m0)
               (v3 : compact_prod (map (field_type' F) (it0 :: p :: m0)))
               (IHf1 : compact_prod (map (field_type' F) (p :: m0)) ->
                       compact_prod (map (field_type' F) (it1 :: f1))) =>
             (fst v3, IHf1 (snd v3))
         end eq_refl v2 IHf0) v1
   end v0 IHf) f v.


Definition list_data {ls: listspec list_structid list_link list_token} (v: elemtype ls): reptype list_struct.
  unfold list_struct.
  pose (add_link_back _ _ v: reptype_structlist _).
  rewrite list_members_eq in r.
  exact (@fold_reptype _ (Tstruct _ _) r).
Defined.

Definition list_cell' (ls: listspec list_structid list_link list_token) sh v p :=
  (field_at_ sh list_struct (StructField list_link :: nil) p) -* (data_at sh list_struct (list_data v) p).

Definition list_cell (ls: listspec list_structid list_link list_token) (sh: Share.t)
   (v: elemtype ls) (p: val) : mpred :=
   !! field_compatible list_struct nil p &&
   struct_pred (all_but_link list_fields)
              (fun it v => withspacer sh
                (field_offset cenv_cs (name_member it) list_fields + sizeof (field_type (name_member it) list_fields))
                (field_offset_next cenv_cs (name_member it) list_fields (co_sizeof (get_co list_structid)))
                (at_offset (data_at_rec sh (field_type (name_member it) list_fields) v) (field_offset cenv_cs (name_member it) list_fields)))
     v p.

Lemma struct_pred_type_changable:
  forall m m' A F v v' p p',
  m=m' ->
  JMeq v v' ->
  (forall it v, F it v p = F it v p') ->
  struct_pred m (A := A) F v p = struct_pred m' (A := A) F v' p'.
Proof.
intros.
subst m'. apply JMeq_eq in H0. subst v'.
induction m. reflexivity.
destruct m.
destruct a; simpl; apply H1.
rewrite !struct_pred_cons2.
f_equal.
auto.
apply IHm.
Qed.

Lemma list_cell_link_join:
  forall (LS: listspec list_structid list_link list_token) sh v p,
   list_cell LS sh v p
   * spacer sh  (field_offset cenv_cs list_link list_fields +
                        sizeof (field_type list_link list_fields))
                        (field_offset_next cenv_cs list_link list_fields
                        (co_sizeof (get_co list_structid)))
           (offset_val 0 p)
   * field_at_ sh list_struct (StructField list_link :: nil) p
     = data_at sh list_struct (list_data v) p.
Proof.
unfold list_cell, data_at_, data_at, field_at_, field_at; intros.
(*destruct (field_compatible_dec list_struct nil p);
  [ | solve [apply pred_ext; normalize]].*)
Admitted.
(*
rewrite <- !gather_prop_left.
rewrite !(prop_true_andp _ _ f).
rewrite (prop_true_andp (field_compatible list_struct (StructField list_link :: nil) p))
   by admit.
normalize.
apply andp_prop_ext.
admit.
intro HV.
clear HV.
change  (nested_field_type list_struct nil) with list_struct.
rewrite (data_at_rec_ind sh list_struct
          (@fold_reptype cs (Tstruct list_structid noattr)
            (@eq_rect members
               (@list_fields cs list_structid list_link LS)
               (fun m : members => @reptype_structlist cs m)
               (@add_link_back
                  (@list_fields cs list_structid list_link LS)
                  (@list_fields cs list_structid list_link LS) v)
               (co_members (@get_co cs list_structid))
               (@list_members_eq cs list_structid list_link LS)))).
simpl.
forget (co_sizeof (get_co list_structid)) as sz.
assert (FT: field_type list_link list_fields = tptr list_struct).
  admit.
pose (P m := fun (it : ident * type) (v0 : reptype (field_type (fst it) m)) =>
   withspacer sh
     (field_offset cenv_cs (fst it) m +
      sizeof (field_type (fst it) m))
     (field_offset_next cenv_cs (fst it) m sz)
     (at_offset (data_at_rec sh (field_type (fst it) m) v0)
        (field_offset cenv_cs (fst it) m))).
fold (P list_fields).
fold (P (co_members (get_co list_structid))).
transitivity
  (at_offset
  (struct_pred (co_members (get_co list_structid))
     (P (co_members (get_co list_structid)))
     (
           (eq_rect list_fields (fun m : members => reptype_structlist m)
              (add_link_back _ _ v) (co_members (get_co list_structid))
              list_members_eq))) (nested_field_offset list_struct nil) p);
 [ | f_equal; f_equal; rewrite unfold_fold_reptype; reflexivity ].
unfold at_offset.
rewrite (data_at_rec_type_changable sh
                      (nested_field_type list_struct (StructField list_link :: nil))
                      (tptr list_struct)
                      (default_val _) Vundef
                      list_link_type)
  by (rewrite by_value_default_val; try reflexivity;
       rewrite list_link_type; reflexivity).
set (ofs := Int.repr (nested_field_offset list_struct (StructField list_link :: nil))).
assert (Hofs: ofs = Int.repr (field_offset cenv_cs list_link list_fields)). {
  unfold ofs.
  clear.
  f_equal.
  unfold list_struct.
  pose proof list_link_type.
  unfold nested_field_offset.
  simpl. rewrite list_members_eq.
  unfold list_struct, nested_field_type in H; simpl in H.
  destruct (compute_in_members list_link (co_members (get_co list_structid))); inv H.
  reflexivity.
  }
revert v; unfold elemtype.
fold (field_type' list_fields).
pose (m := list_fields).
pose (m' := co_members (get_co list_structid)).
set (H := list_members_eq).
clearbody H.
revert H.
change (forall (H: m=m')
  (v : compact_prod (map (field_type' list_fields) (all_but_link m))),
struct_pred (all_but_link m) (P list_fields) v p  *
spacer sh
  (field_offset cenv_cs list_link list_fields +
   sizeof (field_type list_link list_fields))
  (field_offset_next cenv_cs list_link list_fields sz)
  p*
data_at_rec sh (tptr list_struct) Vundef
  (offset_val ofs p) =
struct_pred m'
  (P m')
  (eq_rect m reptype_structlist
     (add_link_back list_fields m v) m' H)
  (offset_val (Int.repr 0) p)).
assert  (MNR := get_co_members_no_replicate list_structid).
fold m' in MNR.
revert MNR.
clearbody m'.
intros.
subst m'.
rewrite <- eq_rect_eq.
assert (In list_link (map fst m)). {
 unfold m.
 rewrite list_members_eq.
 pose proof list_link_type.
 unfold nested_field_type in H.
 unfold list_struct in H. unfold nested_field_rec in H.
 destruct (compute_in_members list_link (co_members (get_co list_structid)))
    eqn:?; inv H.
 apply compute_in_members_true_iff; auto.
}
change (struct_pred (all_but_link m) (P list_fields) v p  *
spacer sh
  (field_offset cenv_cs list_link list_fields +
   sizeof (field_type list_link list_fields))
  (field_offset_next cenv_cs list_link list_fields sz)
  p*
data_at_rec sh (tptr list_struct) Vundef (offset_val ofs p) =
struct_pred m (P list_fields)
  (add_link_back list_fields m v)
  (offset_val (Int.repr 0) p)).
revert MNR H v; clearbody m.
induction m; intros; [inv H | ].
 simpl in H.
 assert (H': In list_link (map fst m) -> fst a <> list_link).
  clear - MNR. unfold members_no_replicate in MNR.
    intros; simpl in *.  destruct (id_in_list (fst a) (map fst m)) eqn:?. inv MNR.
    apply id_in_list_false in Heqb. intro. congruence.
 destruct H.
* (* list_link is the first field *)
clear H'.
destruct a. simpl in H. subst i.
destruct m.
Opaque field_offset. Opaque field_type. simpl.
Transparent field_offset. Transparent field_type.
assert ((if ident_eq list_link list_link then nil else (list_link, t) :: nil) = nil)
  by (rewrite if_true; auto).
simpl in v.
assert (exists v' : compact_prod (map (field_type' list_fields) nil), JMeq v' v).  {
  revert H v.
  clear.
  pose (j := if ident_eq list_link list_link
             then @nil (ident * type) else (list_link, t) :: @nil (ident * type)).
  change (j = nil ->
   forall
     v : compact_prod (map (field_type' list_fields) j),
    exists v' : compact_prod (map (field_type' list_fields) nil), JMeq v' v).
  clearbody j.
  intros; subst. exists v; reflexivity.
}
destruct H0 as [v' ?].
replace (struct_pred
  (if ident_eq list_link list_link then nil else (list_link, t) :: nil)
  (P list_fields) v p) with
  (struct_pred nil (P list_fields) v' p).
Focus 2.
if_tac; [ | congruence]. reflexivity.
Opaque field_offset. Opaque field_type. simpl.
Transparent field_offset. Transparent field_type.
rewrite emp_sepcon.
clear v' H0 H v IHm.
unfold P.
rewrite withspacer_spacer.
unfold at_offset. simpl @fst.
f_equal.
rewrite isptr_offset_val_zero by auto.
auto.
rewrite offset_offset_val, Int.add_zero_l.
rewrite Hofs.
apply equal_f.
apply data_at_rec_type_changable; auto.
rewrite FT. reflexivity.
assert (all_but_link ((list_link,t)::p0::m) = p0::m).
simpl. rewrite if_true by auto; reflexivity.
assert (all_but_link (p0::m) = p0::m). {
   clear - MNR H.
   admit. (* easy enough *)
}
rewrite struct_pred_cons2.
unfold P at 2.
rewrite withspacer_spacer.
rewrite Hofs. unfold at_offset.
rewrite offset_offset_val, Int.add_zero_l.
change (fst (list_link, t)) with list_link.
rewrite isptr_offset_val_zero by auto.
pull_right (spacer sh
  (field_offset cenv_cs list_link list_fields +
   sizeof (field_type list_link list_fields))
  (field_offset_next cenv_cs list_link list_fields sz) p).
f_equal.
rewrite sepcon_comm.
f_equal.
apply equal_f.
apply data_at_rec_type_changable; auto.
apply JMeq_trans with (B:= reptype (field_type list_link list_fields)) (y:= default_val (field_type list_link list_fields)).
rewrite FT. reflexivity.
match goal with |- JMeq ?A ?B => replace A with B end.
apply JMeq_refl.
clear.
revert v.
unfold all_but_link.
unfold add_link_back.
unfold list_rect at 1.
simpl @fst.
destruct (ident_eq list_link list_link); [ | exfalso; congruence]; intro.
simpl. reflexivity.
 apply struct_pred_type_changable; auto.
 clear.
 revert v.
 simpl.
 destruct (ident_eq list_link list_link); [ | exfalso; congruence]; intro.
 simpl. reflexivity.
* (* list link is not the first field *)
 specialize (H' H).
destruct m; [inv H | ].
 rewrite struct_pred_cons2.
 assert (all_but_link (a :: p0 :: m) = a :: all_but_link (p0::m)). {
  clear - MNR H. forget (p0::m) as m'. clear p0 m.
  induction m'. inv H.
  unfold all_but_link; fold all_but_link.
  unfold members_no_replicate in *.
  rewrite map_cons in MNR.
  unfold compute_list_norepet in MNR.
  fold compute_list_norepet in MNR.
  destruct (id_in_list (fst a) (map fst (a0 :: m'))) eqn:?; [discriminate | ].
  simpl in Heqb. rewrite orb_false_iff in Heqb. destruct Heqb.
  apply Pos.eqb_neq in H0.
  apply id_in_list_false in H1.
  simpl in H. destruct H.
  rewrite H in *. rewrite if_false by auto. auto.
  rewrite if_false by congruence. auto.
}
 unfold members_no_replicate in *.
 simpl in MNR.
 destruct ((fst a =? fst p0)%positive || id_in_list (fst a) (map fst m))%bool eqn:?; try discriminate.
 rewrite orb_false_iff in Heqb. destruct Heqb.
  apply Pos.eqb_neq in H1.
  apply id_in_list_false in H2.
  specialize (IHm MNR H).
 destruct p0 as [i t].
(* simpl in v'. *)
  simpl in H1. clear MNR H.
 destruct (ident_eq i list_link).
 + subst i.
  assert (exists v' : compact_prod (map (field_type' list_fields) (a :: m)),
                JMeq v v'). {
   revert v; clear - H0.
   replace (all_but_link ((list_link, t) :: m)) with m in H0
     by (simpl; rewrite if_true by auto; auto).
   rewrite H0. eexists; eauto.
 }
 destruct H as [v' H3].
 simpl in v'.
 destruct m.
 -
  simpl in v'.
  assert (exists v'': compact_prod
                  (map (field_type' list_fields)
                     (all_but_link ((list_link, t) :: nil))), JMeq v'' tt). {
  clear. simpl. rewrite if_true by auto. exists tt; reflexivity.
 }
 destruct H as [v'' H4].
 specialize (IHm v'').
 replace (struct_pred (all_but_link ((list_link, t) :: nil)) (P list_fields) v'' p) with
    (struct_pred nil (P list_fields) tt p) in IHm
  by (apply struct_pred_type_changable; auto; simpl; rewrite if_true; auto).
  change (struct_pred nil (P list_fields) tt p) with emp in IHm.
  rewrite emp_sepcon in IHm.
  rewrite sepcon_assoc. rewrite IHm; clear IHm.
  f_equal.
  assert (exists v4: compact_prod
                  (map (field_type' list_fields) (a::nil)), JMeq v4 v). {
  clear - H1. revert v. simpl. rewrite if_false by auto. rewrite if_true by auto.
  eexists; eauto.
 }
 destruct H as [v4 H5].
  transitivity (struct_pred (a :: nil) (P list_fields) v4 (offset_val (Int.repr 0) p)).
 apply struct_pred_type_changable; auto.
 simpl. rewrite if_false by auto; rewrite if_true by auto. auto.
 admit. (* see proof above *)
 destruct a as [i' t'].
 unfold struct_pred at 1.
  unfold list_rect.
  f_equal.
  clear - H1 H5. simpl in H1.
  admit.  (* tedious *)
  apply struct_pred_type_changable; auto.
  clear - H1 H4 H3.
  simpl in v'.
  admit.  (* tedious *)
  -
  simpl map at 1 in v'. cbv beta iota in v'.
  destruct v' as [va vr].
  assert (exists vr' : compact_prod
              (map (field_type' list_fields)
                 (all_but_link ((list_link, t) :: p0 :: m))),
                JMeq vr vr'). {
  clear - H1; simpl in H1.
  simpl. rewrite if_true by auto. exists vr; eauto.
  } destruct H as [vr' H4].
   specialize (IHm vr').
  replace (struct_pred (all_but_link (a :: (list_link, t) :: p0 :: m)) (P list_fields) v p)
       with (P list_fields a
                (fst (add_link_back list_fields (a :: (list_link, t) :: p0 :: m) v))
                 (offset_val (Int.repr 0) p) *
                struct_pred (all_but_link ((list_link, t) :: p0 :: m)) (P list_fields) vr' p).
  rewrite !sepcon_assoc. f_equal.
  rewrite <- sepcon_assoc.
  rewrite IHm.
  apply struct_pred_type_changable; auto.
  clear - H3 H4 H1.
  admit.  (* tedious *)
  clear - H3 H4 H1 H0.
  transitivity (P list_fields a va p *
                    struct_pred (all_but_link ((list_link, t) :: p0 :: m)) (P list_fields) vr' p).
  f_equal.
  unfold P; rewrite !withspacer_spacer; f_equal. rewrite <- spacer_offset_zero. auto.
  unfold at_offset. rewrite offset_offset_val. rewrite Int.add_zero_l.
  f_equal.
  admit.  (* tedious *)
  assert (exists v6: compact_prod (map (field_type' list_fields) (a :: p0 :: m)),
                JMeq v v6). {
    clear - H1 H0.
    simpl all_but_link at 2 in H0. rewrite if_true in H0 by auto.
 revert v; rewrite H0. intros. exists v; auto.
 } destruct H as [v6 H].
  transitivity (struct_pred (a :: p0 :: m) (P list_fields) v6 p).
  rewrite struct_pred_cons2. f_equal.
  unfold P; rewrite !withspacer_spacer; f_equal.
  unfold at_offset.
  f_equal. rewrite H in H3. clear - H3. apply JMeq_eq in H3. subst; reflexivity.
  apply struct_pred_type_changable; auto.
  simpl. rewrite if_true by auto. auto.
  rewrite H in H3.
  clear - H3 H4.
  eapply JMeq_trans. apply JMeq_sym. apply H4.
  destruct v6.
  clear - H3. simpl.
  apply JMeq_eq in H3. inv H3; auto.
  apply struct_pred_type_changable; auto.
  simpl. rewrite if_false by auto. rewrite if_true by auto. auto.
 +
   assert (all_but_link ((i,t)::m) = (i,t)::all_but_link m).
   simpl. rewrite if_false by auto; auto.
   assert (exists v' :
      (field_type' list_fields a * compact_prod (map (field_type' list_fields) (all_but_link ((i, t) :: m)))), JMeq v v'). {
     clear - H H0 v. revert v; rewrite H0. rewrite H.
   simpl. intros. exists v; reflexivity.
 } destruct H3 as [v' Hv'].
  destruct v' as [v1 vr].
  specialize (IHm vr).
  replace (struct_pred (all_but_link (a :: (i, t) :: m)) (P list_fields) v p)
     with (P list_fields a (fst (add_link_back list_fields (a :: (i, t) :: m) v))
                   (offset_val (Int.repr 0) p) *
              struct_pred (all_but_link ((i, t) :: m)) (P list_fields) vr p).
  rewrite !sepcon_assoc. f_equal.
  rewrite <- sepcon_assoc.
  rewrite IHm. clear IHm.
  apply struct_pred_type_changable; auto.
  admit.  (* tedious *)
  assert (exists v'': compact_prod
      (field_type' list_fields a :: field_type' list_fields (i,t) :: map (field_type' list_fields) (all_but_link m)),
    JMeq v v''). {
    clear - H H0. revert v; rewrite H0. rewrite H. intros; exists v. reflexivity.
  } destruct H3 as [v'' Hv''].
  transitivity (struct_pred (a :: (i,t) :: all_but_link m) (P list_fields) v'' p).
  rewrite struct_pred_cons2.
  f_equal.
  admit.  (* tedious *)
  apply struct_pred_type_changable; auto.
  clear - Hv' Hv''. rewrite Hv'' in Hv'. simpl in v''. destruct v''.
  clear - Hv'.
  admit.  (* tedious *)
  apply struct_pred_type_changable; auto.
  rewrite H0. rewrite H. auto.
Qed.
*)
Lemma list_cell_link_join_nospacer:
  forall (LS: listspec list_structid list_link list_token) sh v p,
   field_offset cenv_cs list_link list_fields +
                        sizeof (field_type list_link list_fields) =
   field_offset_next cenv_cs list_link list_fields
                        (co_sizeof (get_co list_structid)) ->
   list_cell LS sh v p * field_at_ sh list_struct (StructField list_link :: nil) p
     = data_at sh list_struct (list_data v) p.
Proof.
intros.
rewrite <- list_cell_link_join.
unfold spacer. rewrite if_true. rewrite sep_emp. auto.
lia.
Qed.

End LIST1.

Module LsegGeneral.

Section LIST2.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident} {list_token: share -> val -> mpred}.

Fixpoint lseg (ls: listspec list_structid list_link list_token) (dsh psh: share)
            (contents: list (val * elemtype ls)) (x z: val) : mpred :=
 match contents with
 | (p,h)::hs => !! (p=x /\ ~ptr_eq x z) &&
              EX y:val,  !! is_pointer_or_null y &&
              list_token dsh x * list_cell ls dsh h x
              * field_at psh list_struct (StructField list_link ::nil)
                  (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x
              * lseg ls dsh psh hs y z
 | nil => !! (ptr_eq x z) && emp
 end.

Lemma lseg_unfold (ls: listspec list_structid list_link list_token): forall dsh psh contents v1 v2,
    lseg ls dsh psh contents v1 v2 =
     match contents with
     | (p,h)::t => !! (p=v1 /\ ~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_token dsh v1 * list_cell ls dsh h v1
                      * field_at psh list_struct (StructField list_link :: nil)
                          (valinject (nested_field_type list_struct (StructField list_link :: nil)) tail) v1
                      * lseg ls dsh psh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 destruct contents as [ | [? ?] ?]; simpl; auto.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link list_token):
  forall dsh psh l v ,
  is_pointer_or_null v ->
    lseg ls dsh psh l v v = (!!(l=nil) && emp).
Proof.
intros.
rewrite (lseg_unfold ls dsh psh l v v).
destruct l.
f_equiv. f_equiv. apply prop_ext.
split; intro; auto.
unfold ptr_eq.
unfold is_pointer_or_null in H.
destruct Archi.ptr64 eqn:Hp;
destruct v; inv H; auto;
unfold Ptrofs.cmpu; rewrite Ptrofs.eq_true; auto.
destruct p.
rewrite !prop_false_andp; auto.
rewrite ptr_eq_True; tauto.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link list_token) dsh psh (l: list (val * elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (val * elemtype ls), EX y:val,
             !!(l=(x,h)::r  /\ is_pointer_or_null y) &&
             list_token dsh x * list_cell ls dsh h x *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
             lseg ls dsh psh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link list_token): forall dsh psh l x z ,
    lseg ls dsh psh l x z ⊣⊢
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls dsh psh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
apply bi.pure_elim_l; intros.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
apply bi.or_intro_l; auto.
destruct p.
rewrite <- bi.or_intro_r.
unfold lseg_cons.
apply bi.pure_elim_l; intros.
destruct H.
apply bi.exist_elim; intro tail.
normalize.
rewrite <- (bi.exist_intro e).
rewrite <- (bi.exist_intro l).
rewrite <- (bi.exist_intro tail).
repeat rewrite sepcon_andp_prop'.
apply bi.and_intro.
apply bi.pure_intro; auto.
subst.
auto.
subst. auto.
apply bi.or_elim.
rewrite <- bi.pure_and.
apply bi.pure_elim_l; intros []; auto.
unfold lseg_cons.
apply bi.pure_elim_l; intros.
apply bi.exist_elim; intro h.
apply bi.exist_elim; intro r.
apply bi.exist_elim; intro y.
do 3 rewrite sepcon_andp_prop'.
apply bi.pure_elim_l; intros [? ?].
inv H0.
destruct p.
apply bi.or_elim.
rewrite <- bi.pure_and.
apply bi.pure_elim_l; intros [].
inv H0.
unfold lseg_cons.
apply bi.pure_elim_l; intros.
apply bi.exist_elim; intro h.
apply bi.exist_elim; intro r.
apply bi.exist_elim; intro y.
do 3 rewrite sepcon_andp_prop'.
apply bi.pure_elim_l; intros [? ?].
symmetry in H0; inv H0.
rewrite prop_true_andp by auto.
rewrite <- (bi.exist_intro y).
normalize.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link list_token):
   forall p P dsh psh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    (P |-- list_token dsh v1 * list_cell ls dsh h v1 *
             (field_at psh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls dsh psh tail p v2)) ->
    P |-- lseg ls dsh psh ((v1,h)::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. rewrite <- bi.or_intro_r. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  rewrite <- (bi.exist_intro h). rewrite <- (bi.exist_intro tail). rewrite <- (bi.exist_intro p).
    rewrite prop_true_andp by auto.
  rewrite H1; cancel.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link list_token):
  forall dsh psh s v v2,
    ptr_neq v v2 ->
     lseg ls dsh psh s v v2 ⊣⊢ lseg_cons ls dsh psh s v v2.
intros. rewrite lseg_unroll.
apply pred_ext. apply bi.or_elim; auto.
rewrite <- bi.pure_and.
apply bi.pure_elim_l; intros [].
congruence.
apply bi.or_intro_r.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall dsh psh s v,
      typed_true (tptr list_struct) v ->
     lseg ls dsh psh s v nullval ⊣⊢ lseg_cons ls dsh psh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
destruct v; inv H; intuition; try congruence.
intro. apply ptr_eq_e in H.
destruct Archi.ptr64 eqn:Hp; inv H; try done.
intro. simpl in H.
destruct Archi.ptr64; congruence.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R (v v2: val) dsh psh (s: list (val * elemtype ls)),
      (PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R))) |--
                        !! (ptr_neq v v2)) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R))) |--
     EX hryp: elemtype ls * list (val * elemtype ls) * val * val,
      match hryp with (h,r,y,p) =>
       !! (s=(p,h)::r /\ is_pointer_or_null y) &&
       !! (p=v) &&
      PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y v2 ::
                  R)))
        end.
Proof.
intros.
trans
(PROPx P (LOCALx (Q1::Q) (SEPx (lseg_cons ls dsh psh s v v2 :: R)))).
trans
(!! ptr_neq v v2 && PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R)))).
apply bi.and_intro; auto.
apply bi.pure_elim_l; intros.
rewrite lseg_neq; auto.
unfold lseg_cons.
rewrite <- insert_local.
iIntros "(#? & #? & #? & ((% & % & % & % & H) & ?))".
iExists (h, r, y, v).
iDestruct "H" as "(((((% & %) & ?) & ?) & ?) & ?)"; iSplit; auto.
iFrame; auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R e dsh psh s,
      (PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s e nullval :: R))) |--
                        !! (typed_true (tptr list_struct) e)) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s e nullval :: R))) |--
     EX hryp: elemtype ls * list (val * elemtype ls) * val * val,
      match hryp with (h,r,y,p) =>
       !! (s=(p,h)::r /\ is_pointer_or_null y) &&
       !! (p=e)&&
      PROPx P (LOCALx Q
        (SEPx (list_token dsh e :: list_cell ls dsh h e ::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) e ::
                  lseg ls dsh psh r y nullval ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
rewrite H. normalize.
intro.
apply ptr_eq_e in H1. subst.
normalize.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link list_token):
  forall {OK_spec}
      E Delta P Q dsh psh s v v2 R c Post,
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list (val * elemtype ls)) (y: val),
    s=(v,h)::r -> is_pointer_or_null y ->
    semax(OK_spec := OK_spec) E Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v ::
                  field_at psh list_struct (StructField list_link :: nil)
                      (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y v2 ::
                  R)))) c Post) ->
   semax E Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls dsh psh s v v2 :: R))))
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list (val * elemtype ls), EX y: val,
  !!(s = (v, h) :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (list_token dsh v :: list_cell ls dsh h v ::
       field_at psh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type list_struct
                         (StructField list_link :: nil)) y) v ::
        lseg ls dsh psh r y v2 :: R)))).
go_lowerx; entailer!.
Exists h r y.
entailer!.
Intros h r y.
apply semax_extract_prop; intros [? ?].
eapply H0; eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall OK_spec
      E Delta P Q dsh psh s v R c Post,
   (ENTAIL Delta, PROPx P (LOCALx Q
            (SEPx (lseg ls dsh psh s v nullval :: R))) ⊢
                        !!(typed_true (tptr list_struct) v))  ->
  (forall (h: elemtype ls) (r: list (val * elemtype ls)) (y: val),
    s=(v,h)::r -> is_pointer_or_null y ->
    semax(OK_spec := OK_spec) E Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v ::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y nullval ::
                  R)))) c Post) ->
   semax E Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls dsh psh s v nullval :: R))))
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
rewrite H.
normalize.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link list_token):
    forall dsh psh p q, lseg ls dsh psh nil p q ⊣⊢ !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply bi.or_elim.
 rewrite <- bi.pure_and; apply bi.pure_elim_l; intros []; auto.
 unfold lseg_cons. by normalize.
 rewrite <- bi.or_intro_l. rewrite <- bi.and_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link list_token):
     forall dsh psh h r x z ,
    lseg ls dsh psh (h::r) x z ⊣⊢
        !!(x = fst h /\ ~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_token dsh x * list_cell ls dsh (snd h) x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
   lseg ls dsh psh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 apply bi.or_elim.
 rewrite <- bi.pure_and.
 apply bi.pure_elim_l; intros [].
 inv H0.
 unfold lseg_cons.
 normalize.
 symmetry in H0; inv H0.
 rewrite <- (bi.exist_intro y). entailer!. auto.
 normalize. destruct h as [p h]. simpl in *.
 rewrite <- bi.or_intro_r.
 unfold lseg_cons.
 rewrite prop_true_andp by auto.
  rewrite <- !bi.exist_intro.
  cancel.
  simpl; entailer!.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link list_token)
           dsh psh (l: list (val * elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (val * elemtype ls), EX y:val,
             !!(l=r++(y,h)::nil /\ is_pointer_or_null y)  &&
                       list_token dsh y * list_cell ls dsh h y *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link list_token): forall dsh psh l x h y w z,
             sepalg.nonidentity psh ->
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh l x y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls dsh psh (l++(y,h)::nil) x z * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z.
Proof.
intros. rename H into SH.
assert (SZ: 0 < sizeof (nested_field_type list_struct (DOT list_link))).
  unfold sizeof; rewrite list_link_type; simpl; destruct Archi.ptr64; computable.
rewrite (field_at_isptr _ _ _ _ z).
normalize.
revert x; induction l; simpl; intros.
*
normalize.
 rewrite <- (bi.exist_intro z).
 entailer!.
*
destruct a as [v el].
iIntros "((H & (% & %) & % & ? & lseg) & Hz)"; subst.
iAssert ⌜~ptr_eq x z⌝ as %?.
{ iStopProof; entailer!. }
iPoseProof (IHl with "[$H $lseg $Hz]") as "(? & ?)".
iFrame.
iSplit; first done.
iExists y0; iFrame.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link list_token): forall dsh psh l x h y,
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) nullval) y *
             lseg ls dsh psh l x y
   |--   lseg ls dsh psh (l++(y,h)::nil) x nullval.
Proof.
intros.
revert x; induction l; simpl; intros.
*
Exists nullval; entailer!.
*
destruct a as [v el].
iIntros "(H & (% & %) & % & ? & lseg)"; subst.
iAssert ⌜~ptr_eq x nullval⌝ as %?.
{ iStopProof; entailer!. }
iPoseProof (IHl with "[$H $lseg]") as "?".
iSplit; first done.
iExists y0; iFrame.
Qed.


Lemma lseg_cons_right_list (ls: listspec list_structid list_link list_token): forall dsh psh l l' x h y z,
    sepalg.nonidentity psh ->
             list_token dsh y * list_cell ls dsh h y
           * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y
           * lseg ls dsh psh l x y
           * lseg ls dsh psh l' z nullval
   |--   lseg ls dsh psh (l++(y,h)::nil) x z * lseg ls dsh psh l' z nullval.
Proof.
intros.
destruct l'.
rewrite lseg_nil_eq.
entailer!.
rewrite <- lseg_cons_right_null; cancel.

rewrite lseg_cons_eq.
Intros u. Exists u. subst z.
iIntros "(H & (? & Hp) & ?)".
iPoseProof (lseg_cons_right_neq with "[$H $Hp]") as "?"; first done.
iStopProof; entailer!.
Qed.

Lemma lseg_unroll_right (ls: listspec list_structid list_link list_token): forall sh sh' l x z ,
    lseg ls sh sh' l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh sh' l x z.
Abort.  (* not likely true *)


Lemma lseg_local_facts:
  forall ls dsh psh contents p q,
     lseg ls dsh psh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply bi.pure_elim_l; intro.
unfold ptr_eq in H.
apply bi.pure_intro.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
unfold Int.cmpu in H.
destruct H as [? [? ?]].
apply int_eq_e in H0.
apply int_eq_e in H1. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
unfold Int64.cmpu in H.
destruct H as [? [? ?]].
apply int64_eq_e in H0.
apply int64_eq_e in H1. subst.
split3; auto; done.
destruct q; try contradiction.
destruct H; subst.
unfold Ptrofs.cmpu in H0.
apply ptrofs_eq_e in H0.
subst. tauto.
destruct p0.
normalize.
rewrite field_at_isptr.
Intros; entailer!.
split. intro; subst q.
contradiction H. normalize.
intros. discriminate.
Qed.

Definition lseg_cell  (ls: listspec list_structid list_link list_token)
    (dsh psh : share)
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_token dsh x * list_cell ls dsh v x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link list_token) (dsh psh : share) (h : elemtype ls)
   (r : list (val * elemtype ls))
  (x x' z : val), lseg ls dsh psh ((x',h) :: r) x z ⊣⊢
  !!(x=x' /\ ~ ptr_eq x z) && (EX  y : val, lseg_cell ls dsh psh h x y * lseg ls dsh psh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
 normalize.
Qed.

Lemma list_append: forall {dsh psh: share}
  {ls : listspec list_structid list_link list_token} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls dsh psh x tl tl' * P tl |-- False) ->
  (lseg ls dsh psh ct1 hd mid) * lseg ls dsh psh ct2 mid tl * P tl|--
  (lseg ls dsh psh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  revert hd; induction ct1; simpl; intros; auto.
  *
  normalize.
  *
  destruct a  as [v a].
  Intros y.
  apply bi.and_intro.
  destruct (eq_dec hd tl); last by entailer!.
  subst; clear IHct1.
  unfold lseg_cell in H.
  specialize (H a y).
  rewrite prop_true_andp in H by auto.
  iIntros "(((? & ?) & ?) & ?)"; iDestruct (H with "[$]") as "[]".
  go_lower.sep_apply IHct1.
  Exists y; entailer!.
Qed.

Lemma list_append_null:
  forall
   (ls: listspec list_structid list_link list_token)
   (dsh psh: share)
   (hd mid: val) ct1 ct2,
   lseg ls dsh psh ct1 hd mid * lseg ls dsh psh ct2 mid nullval |--
   lseg ls dsh psh (ct1++ct2) hd nullval.
Proof.
intros.
 rewrite <- bi.sep_emp.
 rewrite (list_append _ _ _ _ _ (fun _ => emp)).
 iIntros "($ & _)".
 intros.
  unfold lseg_cell. simpl. saturate_local. destruct H. contradiction H.
Qed.

Lemma sizeof_list_struct_pos (LS: listspec list_structid list_link list_token) :
   sizeof list_struct > 0.
Admitted.

End LIST2.

#[export] Hint Rewrite @lseg_nil_eq : norm.

#[export] Hint Rewrite @lseg_eq using reflexivity: norm.

#[export] Hint Resolve lseg_local_facts : saturate_local.
End LsegGeneral.

Module LsegSpecial.
Import LsegGeneral.

Section LIST.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident} {list_token: share -> val -> mpred}.

Definition lseg (ls: listspec list_structid list_link list_token) (sh: share)
   (contents: list (elemtype ls)) (x y: val) : mpred :=
    EX al:list (val*elemtype ls),
          !! (contents = map snd al) &&
             LsegGeneral.lseg ls sh sh al x y.

Lemma lseg_unfold (ls: listspec list_structid list_link list_token): forall sh contents v1 v2,
    lseg ls sh contents v1 v2 ⊣⊢
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_token sh v1 * list_cell ls sh h v1
                      * field_at sh list_struct (StructField list_link :: nil)
                          (valinject (nested_field_type list_struct (StructField list_link :: nil)) tail) v1
                      *  lseg ls sh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 unfold lseg.
 revert v1; induction contents; intros.
 apply pred_ext.
 normalize. destruct al; inv H.
 rewrite LsegGeneral.lseg_nil_eq; auto.
 rewrite <- (bi.exist_intro nil).
 apply bi.pure_elim_l; intro.
 normalize.
 apply pred_ext.
 apply bi.exist_elim; intros [ | [v1' a'] al].
 Intros. inv H.
 apply bi.pure_elim_l; intro.
 symmetry in H; inv H.
 rewrite LsegGeneral.lseg_cons_eq; auto.
 apply bi.pure_elim_l; intros [? ?].
 simpl in H;  subst v1'.
 apply bi.exist_elim; intro y.
 normalize. rewrite <- (bi.exist_intro y). normalize.
 rewrite <- (bi.exist_intro al); normalize.
 Intros tail al.
 rewrite <- (bi.exist_intro ((v1,a)::al)); entailer!.
 simpl.
 normalize. rewrite <- (bi.exist_intro tail). entailer!.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link list_token):
  forall sh l v ,
  is_pointer_or_null v ->
    lseg ls sh l v v ⊣⊢ !!(l=nil) && emp.
Proof.
intros.
unfold lseg.
apply pred_ext.
normalize.
rewrite LsegGeneral.lseg_eq by auto. normalize.
rewrite <- (bi.exist_intro nil).
normalize.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link list_token) sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val,
             !!(l=h::r  /\ is_pointer_or_null y) &&
             list_token sh x * list_cell ls sh h x *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
              lseg ls sh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link list_token): forall sh l x z ,
    lseg ls sh l x z ⊣⊢
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls sh l x z.
Proof.
intros.
unfold lseg, lseg_cons.
apply pred_ext.
*
apply bi.exist_elim; intros.
apply bi.pure_elim_l; intro.
rewrite LsegGeneral.lseg_unroll.
apply bi.or_elim; [rewrite <- bi.or_intro_l | rewrite <- bi.or_intro_r].
rewrite <- bi.pure_and; apply bi.pure_elim_l; intros [].
entailer!.
unfold LsegGeneral.lseg_cons.
apply bi.pure_elim_l; intro.
rewrite prop_true_andp by auto.
apply bi.exist_mono; intro h.
apply bi.exist_elim; intro r; rewrite <- (bi.exist_intro (map snd r)).
apply bi.exist_mono; intro y.
normalize.
subst l.
unfold lseg.
cancel.
rewrite <- (bi.exist_intro r); normalize.
*
apply bi.or_elim.
rewrite <- bi.pure_and; apply bi.pure_elim_l; intros [].
rewrite <- (bi.exist_intro nil).
simpl. entailer!.
apply bi.pure_elim_l; intro.
apply bi.exist_elim; intro h.
apply bi.exist_elim; intro r.
apply bi.exist_elim; intro y.
normalize.
unfold lseg.
normalize.
rewrite <- (bi.exist_intro ((x,h)::al)).
normalize.
simpl.
normalize.
rewrite <- (bi.exist_intro y).
entailer!.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link list_token):
   forall p P sh h (tail: list (elemtype ls)) v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    (P |-- list_token sh v1 * list_cell ls sh h v1 *
             (field_at sh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls sh tail p v2)) ->
    P |-- lseg ls sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. rewrite <- bi.or_intro_r. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  Exists h tail p.
    rewrite prop_true_andp by auto.
 rewrite H1; entailer!.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link list_token):
  forall sh s v v2,
    ptr_neq v v2 ->
     lseg ls sh s v v2 ⊣⊢ lseg_cons ls sh s v v2.
Proof.
intros. rewrite lseg_unroll.
apply pred_ext. apply bi.or_elim; auto.
rewrite <- bi.pure_and.
apply bi.pure_elim_l; intros [].
congruence.
apply bi.or_intro_r.
Qed.

Opaque Archi.ptr64.

Lemma lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg ls sh s v nullval ⊣⊢ lseg_cons ls sh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
unfold typed_true, strict_bool_val in H.
simpl in H.
destruct Archi.ptr64 eqn:Hp.
*
destruct v; inversion H; clear H.
destruct (Int64.eq i Int64.zero); inversion H1.
intro; apply ptr_eq_e in H; inv H.
*
destruct v; inversion H; clear H.
destruct (Int.eq i Int.zero); inversion H1.
intro; apply ptr_eq_e in H; inv H.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R (v v2: val) sh (s: list (elemtype ls)),
      (PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s v v2 :: R))) |--
                        !! (ptr_neq v v2)) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s v v2 :: R))) |--
     EX hryp: elemtype ls * list (elemtype ls) * val,
      match hryp with (h,r,y) =>
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q
        (SEPx (list_token sh v :: list_cell ls sh h v::
                  field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                   lseg ls sh r y v2 ::
                  R)))
        end.
Proof.
intros.
trans
(PROPx P (LOCALx (Q1::Q) (SEPx (lseg_cons ls sh s v v2 :: R)))).
trans
(!! (ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s v v2 :: R)))).
apply bi.and_intro; auto.
split => rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl; monPred.unseal.
unfold lift1; simpl.
 repeat (apply bi.pure_elim_l; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply bi.sep_mono; auto.
rewrite lseg_neq; auto.
split => rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl; monPred.unseal.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply bi.pure_elim_l; intro.
 apply bi.pure_elim_l; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply bi.pure_elim_l; intro.
 Intros h r y.
 subst.
 rewrite <- (bi.exist_intro (h,r,y)); simpl.
 repeat rewrite prop_true_andp by auto.
 cancel.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R e sh s,
      (PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s e nullval :: R))) |--
                        !!(typed_true (tptr list_struct) e)) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls sh s e nullval :: R))) |--
     EX hryp: elemtype ls * list (elemtype ls) * val,
      match hryp with (h,r,y) =>
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q
        (SEPx (list_token sh e :: list_cell ls sh h e ::
                  field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) e ::
                   lseg ls sh r y nullval ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
rewrite H. normalize.
destruct e; inv H0; try congruence; auto.
intro. apply ptr_eq_e in H0.
destruct Archi.ptr64; inv H0.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link list_token):
  forall Espec
      E Delta P Q sh s v v2 R c Post,
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val),
    s=h::r -> is_pointer_or_null y ->
    semax E Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token sh v :: list_cell ls sh h v ::
                  field_at sh list_struct (StructField list_link :: nil)
                      (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                   lseg ls sh r y v2 ::
                  R)))) c Post) ->
   semax(OK_spec := Espec) E Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls sh s v v2 :: R))))
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list (elemtype ls), EX y: val,
  !!(s = h :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (list_token sh v :: list_cell ls sh h v ::
       field_at sh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type list_struct
                         (StructField list_link :: nil)) y) v ::
        lseg ls sh r y v2 :: R)))).
go_lowerx; entailer.  (* Intros h r y should work here, but doesn't. *)
Exists h r y.
entailer!.
Intros h r y.
apply semax_extract_prop; intros [? ?].
eapply H0; eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall Espec
      E Delta P Q sh s v R c Post,
      ENTAIL Delta, PROPx P (LOCALx Q
            (SEPx (lseg ls sh s v nullval :: R))) |--
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val),
    s=h::r -> is_pointer_or_null y ->
    semax(OK_spec := Espec) E Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token sh v :: list_cell ls sh h v ::
                  field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                   lseg ls sh r y nullval ::
                  R)))) c Post) ->
   semax E Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls sh s v nullval :: R))))
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
rewrite H.
normalize.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link list_token):
    forall sh p q, lseg ls sh nil p q ⊣⊢ !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 - apply bi.or_elim.
   + rewrite <- bi.pure_and.
     apply bi.pure_elim_l; intros []; auto.
   + unfold lseg_cons. by normalize.
 - rewrite <- bi.or_intro_l.
   apply bi.pure_elim_l; intros; auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link list_token):
     forall sh h r x z,
    lseg ls sh (h::r) x z ⊣⊢
        !!(~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_token sh x * list_cell ls sh h x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
   lseg ls sh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 - apply bi.or_elim.
   + rewrite <- bi.pure_and.
     apply bi.pure_elim_l; intros []; discriminate.
   + unfold lseg_cons. normalize. inv H0.
     Exists y; entailer!.
 - rewrite <- bi.or_intro_r.
   Intros y.
   unfold lseg_cons.
   apply bi.and_intro; first auto.
   Exists h r y; entailer!.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link list_token)
           sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val,
             !!(l=r++(h::nil) /\ is_pointer_or_null y)  &&
                       list_token sh y * list_cell ls sh h y *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
              lseg ls sh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link list_token): forall sh l x h y w z,
       sepalg.nonidentity sh ->
             list_token sh y * list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls sh l x y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls sh (l++h::nil) x z * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z.
Proof.
intros.
unfold lseg.
normalize.
Exists (al ++ (y,h)::nil).
rewrite prop_true_andp by (rewrite map_app; reflexivity).
apply LsegGeneral.lseg_cons_right_neq; auto.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link list_token): forall sh l x h y,
             list_token sh y * list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) nullval) y *
             lseg ls sh l x y
   |--   lseg ls sh (l++h::nil) x nullval.
Proof.
intros.
unfold lseg.
normalize.
Exists (al ++ (y,h)::nil).
rewrite prop_true_andp by (rewrite map_app; reflexivity).
apply LsegGeneral.lseg_cons_right_null.
Qed.


Lemma lseg_cons_right_list (ls: listspec list_structid list_link list_token): forall sh l l' x h y z,
              sepalg.nonidentity sh ->
             list_token sh y * list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls sh l x y * lseg ls sh l' z nullval
   |--   lseg ls sh (l++h::nil) x z * lseg ls sh l' z nullval.
Proof.
intros.
destruct l'.
rewrite lseg_nil_eq.
normalize.
rewrite lseg_cons_right_null; auto.
rewrite lseg_cons_eq.
Intros u.
Exists u.
rewrite !prop_true_andp by auto.
iIntros "(H & (? & Hz) & ?)".
iDestruct (lseg_cons_right_neq with "[$H $Hz]") as "($ & $)"; first done.
iFrame.
Qed.

Lemma lseg_unroll_right (ls: listspec list_structid list_link list_token): forall sh l x z ,
    lseg ls sh l x z ⊣⊢ (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)

Lemma lseg_local_facts:
  forall ls sh contents p q,
     lseg ls sh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
unfold lseg.
normalize.
rewrite LsegGeneral.lseg_local_facts.
normalize.
split; auto.
rewrite H.
clear.
destruct al; simpl; intuition; try congruence.
Qed.

Definition lseg_cell (ls: listspec list_structid list_link list_token)
    (sh : share)
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_token sh x * list_cell ls sh v x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link list_token) (sh : share) (h : elemtype ls)
   (r : list (elemtype ls))
  (x z : val), lseg ls sh (h :: r) x z ⊣⊢
  !!(~ ptr_eq x z) && (EX  y : val, lseg_cell ls sh h x y * lseg ls sh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
 normalize.
Qed.

Lemma list_append: forall {sh: share}
  {ls : listspec list_structid list_link list_token} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls sh x tl tl' * P tl |-- False) ->
  (lseg ls sh ct1 hd mid) * lseg ls sh ct2 mid tl * P tl|--
  (lseg ls sh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  unfold lseg.
 normalize.
 rewrite LsegGeneral.list_append; [ | intros; apply (H _ tl')].
 unfold lseg_cell, LsegGeneral.lseg_cell.
 entailer.
 Exists (al++a).
 rewrite prop_true_andp; auto.
 rewrite map_app; reflexivity.
Qed.

Lemma list_append_null:
  forall
   (ls: listspec list_structid list_link list_token)
   (sh: share)
   (hd mid: val) ct1 ct2,
   lseg ls sh ct1 hd mid * lseg ls sh ct2 mid nullval |--
   lseg ls sh (ct1++ct2) hd nullval.
Proof.
intros.
 rewrite <- bi.sep_emp.
 rewrite (list_append _ _ _ _ _ (fun _ => emp)).
 iIntros "($ & _)".
 intros.
  unfold lseg_cell. simpl. saturate_local. destruct H. contradiction H.
Qed.

Lemma list_cell_valid_pointer:
  forall (LS: listspec list_structid list_link list_token) (sh: Share.t) v p,
   sepalg.nonidentity sh ->
   field_offset cenv_cs list_link list_fields + sizeof (field_type list_link list_fields)
   = field_offset_next cenv_cs list_link list_fields  (co_sizeof (get_co list_structid)) ->
   list_cell LS sh v p * field_at_ sh list_struct (StructField list_link::nil) p
  |-- valid_pointer p.
Proof.
  intros ? ? ? ? NON_ID ?.
 rewrite list_cell_link_join_nospacer; auto.
 unfold data_at_, field_at_, data_at.
 saturate_local.
 rewrite field_at_valid_ptr; auto.
 2: {
 change (nested_field_type list_struct nil) with list_struct.
 apply LsegGeneral.sizeof_list_struct_pos. }
 unfold field_address.
 if_tac; auto; contradiction.
Qed.

Lemma lseg_valid_pointer:
  forall (ls : listspec list_structid list_link list_token) sh contents p q R,
   sepalg.nonidentity sh ->
   field_offset cenv_cs list_link list_fields + sizeof (field_type list_link list_fields)
   = field_offset_next cenv_cs list_link list_fields  (co_sizeof (get_co list_structid)) ->
    (R |-- valid_pointer q) ->
    R * lseg ls sh contents p q |-- valid_pointer p.
Proof.
intros ? ? ? ? ? ? NON_ID ? ?.
destruct contents.
rewrite lseg_nil_eq, H0; entailer!.
unfold lseg; simpl.
Intros al.
destruct al; inv H1.
rewrite LsegGeneral.lseg_cons_eq.
Intros y.
subst; destruct p0 as [p z]; simpl in *.
iIntros "(? & ((? & cell) & Hp) & ?)".
iPoseProof (list_cell_valid_pointer with "[$cell Hp]") as "$"; auto.
iStopProof; cancel.
Qed.

End LIST.

#[export] Hint Rewrite @lseg_nil_eq : norm.
#[export] Hint Rewrite @lseg_eq using reflexivity: norm.
#[export] Hint Resolve lseg_local_facts : saturate_local.

Ltac resolve_lseg_valid_pointer :=
match goal with
 | |- ?Q |-- valid_pointer ?p =>
   match Q with context [lseg ?A ?B ?C p ?q] =>
   repeat rewrite bi.sep_assoc;
   pull_right (lseg A B C p q);
   apply lseg_valid_pointer; [auto | reflexivity | ];
   auto 50 with valid_pointer
   end
 end.

#[export] Hint Extern 10 (_ |-- valid_pointer _) =>
   resolve_lseg_valid_pointer : valid_pointer.

Lemma list_cell_local_facts:
  forall {cs: compspecs} {list_structid list_link: ident}{list_token}
    (ls: listspec list_structid list_link list_token) sh v p,
   list_cell ls sh v p |-- !! field_compatible list_struct nil p.
Proof.
intros.
unfold list_cell.
normalize.
Qed.
#[export] Hint Resolve list_cell_local_facts : saturate_local.

End LsegSpecial.

Module Links.

Section LIST2.
Context {cs: compspecs}.
Context  {list_structid: ident} {list_link: ident}{list_token: share -> val -> mpred}.

Definition vund  (ls: listspec list_structid list_link list_token) : elemtype ls :=
 compact_prod_gen
      (fun it => default_val (field_type (name_member it) list_fields)) (@all_but_link list_link  list_fields).

Definition lseg (ls: listspec list_structid list_link list_token) (dsh psh: share)
            (contents: list val) (x z: val) : mpred :=
  LsegGeneral.lseg ls dsh psh (map (fun v => (v, vund ls)) contents) x z.

Lemma nonreadable_list_cell_eq:
  forall (ls: listspec list_structid list_link list_token) sh v v' p,
    ~ readable_share sh ->
   list_cell ls sh v p ⊣⊢ list_cell ls sh v' p.
Proof.
unfold list_cell; intros.
 destruct (field_compatible_dec list_struct nil p);
    [ | solve [ apply pred_ext; normalize ]].
 f_equiv.
 revert v v'; unfold elemtype.
 set (m := all_but_link list_fields).
 assert (PLAIN: plain_members m = true). {
   generalize list_plain. subst m. set (al := list_fields).
   induction al; simpl; intros; auto. 
   destruct a; [ | discriminate].
   if_tac; auto.
 }
 clearbody m.
 induction m; intros.
 reflexivity.
 destruct a as [i t|]; [ |discriminate].
 assert (field_compatible (field_type i list_fields) nil
  (offset_val (field_offset cenv_cs i list_fields) p))
    by  admit.  (* need to adjust the induction hypothesis to prove this *)
 destruct m as [ | [i' t'|]]; [ | | discriminate].
 + Opaque field_type field_offset.
 clear IHm; simpl.
 Transparent field_type field_offset.
 rewrite !withspacer_spacer.
 f_equiv.
 admit. (* apply nonreadable_data_at_rec_eq; auto. *) (* list_cell should be defined by field_at instead of data_at_rec. *)
 +
 rewrite !struct_pred_cons2.
 rewrite !withspacer_spacer.
 f_equiv. f_equiv.
 * admit. (* unfold at_offset. apply nonreadable_data_at_rec_eq; auto.*)
 * apply IHm.
   simpl; auto.
Admitted.

Lemma cell_share_join:
  forall (ls: listspec list_structid list_link list_token) ash bsh psh p v,
   sepalg.join ash bsh psh ->
   list_cell ls ash v p * list_cell ls bsh v p ⊣⊢ list_cell ls psh v p.
Proof.
 intros.
 unfold list_cell.
 destruct (field_compatible_dec list_struct nil p);
    [ | solve [ apply pred_ext; normalize ]].
 normalize.
 revert v; unfold elemtype.
 set (m := all_but_link list_fields).
 assert (PLAIN: plain_members m = true). {
   generalize list_plain. subst m. set (al := list_fields).
   induction al; simpl; intros; auto. 
   destruct a; [ | discriminate].
   if_tac; auto.
 }
 clearbody m.
 induction m; intros.
 simpl. apply bi.emp_sep.
 destruct a as [i t|]; [ | discriminate].
 assert (field_compatible (field_type i list_fields) nil
  (offset_val (field_offset cenv_cs i list_fields) p))
    by  admit.  (* need to adjust the induction hypothesis to prove this *)
 destruct m as [ | [i' t'|]]; [ | | discriminate].
 +
 clear IHm; simpl. rewrite !withspacer_spacer.
(* rewrite assoc.
 match goal with |- ?A * ?B * ?C * ?D = _ =>
    pull_left C; pull_left A
 end.
 rewrite sepcon_assoc. f_equal.
 unfold spacer. if_tac. rewrite emp_sepcon; auto.
 unfold at_offset.
 apply memory_block_share_join; auto.
 unfold at_offset.
 assert (isptr p) by (auto with field_compatible).
 destruct p; try inversion H1.
 apply data_at_rec_share_join; auto.
 +
 rewrite !struct_pred_cons2.
 rewrite !withspacer_spacer.
 match goal with |- (?A * ?B * ?C) * (?A' * ?B' * ?C') = _ =>
   transitivity ((A * A') * (B * B') * (C * C'))
 end.
 rewrite <- ! sepcon_assoc.
 repeat match goal with |- _ * ?A = _ => pull_right A; f_equal end.
 f_equal. f_equal.
 unfold spacer. if_tac. apply sepcon_emp.
 unfold at_offset.
 apply memory_block_share_join; auto.
 unfold at_offset.
 assert (isptr p) by (auto with field_compatible).
 destruct p; try inversion H1.
 apply data_at_rec_share_join; auto.
 apply IHm. auto.*)
Admitted.

Lemma join_cell_link (ls: listspec list_structid list_link list_token):
  forall v' ash bsh psh p v,
   sepalg.join ash bsh psh ->
  ~ (readable_share ash) ->
    readable_share bsh ->
   list_cell ls ash v' p * list_cell ls bsh v p ⊣⊢ list_cell ls psh v p.
 Proof.
 intros.
 rewrite (nonreadable_list_cell_eq _ _ v' v _ H0).
 apply cell_share_join; auto.
Qed.

Lemma lseg_unfold (ls: listspec list_structid list_link list_token): forall dsh psh contents v1 v2,
    lseg ls dsh psh contents v1 v2 =
     match contents with
     | p::t => !! (p=v1 /\ ~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_token dsh v1 * list_cell ls dsh (vund ls) v1
                      * field_at psh list_struct (StructField list_link :: nil)
                          (valinject (nested_field_type list_struct (StructField list_link :: nil)) tail) v1
                      * lseg ls dsh psh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros.
 unfold lseg.
 rewrite LsegGeneral.lseg_unfold.
 revert v1; induction contents; simpl; intros; auto.
Qed.

Lemma lseg_eq (ls: listspec list_structid list_link list_token):
  forall dsh psh l v ,
  is_pointer_or_null v ->
    lseg ls dsh psh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold ls dsh psh l v v).
destruct l.
f_equiv. f_equiv. apply prop_ext.
split; intro; auto.
normalize.
rewrite !prop_false_andp; auto.
rewrite ptr_eq_True; tauto.
Qed.

Definition lseg_cons (ls: listspec list_structid list_link list_token) dsh psh
           (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX h:(elemtype ls), EX r:list val, EX y:val,
             !!(l=x::r  /\ is_pointer_or_null y) &&
             list_token dsh x * list_cell ls dsh h x *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
             lseg ls dsh psh r y z.

Lemma lseg_unroll (ls: listspec list_structid list_link list_token): forall dsh psh l x z ,
    ~ (readable_share dsh) ->
    lseg ls dsh psh l x z ⊣⊢
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls dsh psh l x z.
Proof.
intros.
rename H into NR.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
apply bi.pure_elim_l; intros.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
apply bi.or_intro_l; auto.
rewrite <- bi.or_intro_r.
unfold lseg_cons.
apply bi.pure_elim_l; intros.
destruct H.
subst x.
apply bi.exist_elim; intro tail.
rewrite (prop_true_andp (~ptr_eq v z)) by auto.
Exists (vund ls) l tail.
entailer!.
normalize.
apply bi.or_elim.
apply bi.pure_elim_l; intros [].
auto.
unfold lseg_cons.
Intros h r y.
inv H0.
apply bi.or_elim.
rewrite <- bi.pure_and; apply bi.pure_elim_l; intros [].
inv H0.
unfold lseg_cons.
Intros h r y.
symmetry in H0; inv H0.
 rewrite prop_true_andp by auto.
Exists y.
entailer!.
rewrite nonreadable_list_cell_eq; auto.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_structid list_link list_token):
   forall p P dsh psh h tail v1 v2,
    ~ (readable_share dsh) ->
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    (P |-- list_token dsh v1 * list_cell ls dsh h v1 *
             (field_at psh list_struct (StructField list_link :: nil)
                   (valinject (nested_field_type list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls dsh psh tail p v2)) ->
    P |-- lseg ls dsh psh (v1::tail) v1 v2.
Proof. intros. rewrite lseg_unroll by auto. rewrite <- bi.or_intro_r. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  Exists h tail p.
    rewrite prop_true_andp by auto.
  rewrite H2; cancel.
Qed.

Lemma lseg_neq (ls: listspec list_structid list_link list_token):
  forall dsh psh s v v2,
    ~ (readable_share dsh) ->
    ptr_neq v v2 ->
     lseg ls dsh psh s v v2 ⊣⊢ lseg_cons ls dsh psh s v v2.
Proof.
intros. rewrite lseg_unroll by auto.
apply pred_ext. apply bi.or_elim; auto.
rewrite <- bi.pure_and; apply bi.pure_elim_l; intros [].
congruence.
apply bi.or_intro_r.
Qed.

Lemma lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall dsh psh s v,
    ~ (readable_share dsh) ->
      typed_true (tptr list_struct) v ->
     lseg ls dsh psh s v nullval ⊣⊢ lseg_cons ls dsh psh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq; auto.
unfold typed_true, strict_bool_val in H0; simpl in H0.
destruct Archi.ptr64 eqn:?;
  destruct v; inv H0;
  first [ revert H2; simple_if_tac; discriminate | intro Hx; inv Hx]. 
Qed.

Lemma unfold_lseg_neq (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R (v v2: val) dsh psh (s: list val),
    ~ (readable_share dsh) ->
      (PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R))) |--
                        !! (ptr_neq v v2)) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R))) |--
     EX hryp: elemtype ls * list val * val * val,
      match hryp with (h,r,y,p) =>
       !! (s=p::r /\ is_pointer_or_null y) &&
       !! (p=v) &&
      PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y v2 ::
                  R)))
        end.
Proof.
intros.
trans
(PROPx P (LOCALx (Q1::Q) (SEPx (lseg_cons ls dsh psh s v v2 :: R)))).
trans
(!! (ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s v v2 :: R)))).
apply bi.and_intro; auto.
split => rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl; monPred.unseal.
unfold lift1; simpl.
 repeat (apply bi.pure_elim_l; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply bi.sep_mono; auto.
rewrite lseg_neq; auto.
split => rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl; monPred.unseal.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply bi.pure_elim_l; intro.
 apply bi.pure_elim_l; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply bi.pure_elim_l; intro.
 Intros h r y.
 repeat rewrite sepcon_andp_prop'.
 subst; simpl.
 Exists (h, r, y, v); simpl; entailer!.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_structid list_link list_token):
   forall P Q1 Q R e dsh psh s,
    ~ (readable_share dsh) ->
      (PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s e nullval :: R))) |--
                        !! (typed_true (tptr list_struct) e)) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (lseg ls dsh psh s e nullval :: R))) |--
     EX hryp: elemtype ls * list val * val * val,
      match hryp with (h,r,y,p) =>
       !! (s=p::r /\ is_pointer_or_null y) &&
       !! (p = e) &&
      PROPx P (LOCALx Q
        (SEPx (list_token dsh e :: list_cell ls dsh h e ::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) e ::
                  lseg ls dsh psh r y nullval ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq; auto.
rewrite H0. normalize.
unfold local. super_unfold_lift.
unfold nullval. destruct e; inv H1; try congruence; auto.
intro. apply ptr_eq_e in H1.
destruct Archi.ptr64; inv H1.
Qed.

Lemma semax_lseg_neq (ls: listspec list_structid list_link list_token):
  forall Espec
      E Delta P Q dsh psh s v v2 R c Post,
    ~ (readable_share dsh) ->
    ~ (ptr_eq v v2) ->
  (forall (h: elemtype ls) (r: list val) (y: val),
    s=v::r -> is_pointer_or_null y ->
    semax(OK_spec := Espec) E Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v ::
                  field_at psh list_struct (StructField list_link :: nil)
                      (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y v2 ::
                  R)))) c Post) ->
   semax E Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls dsh psh s v v2 :: R))))
       c Post.
Proof.
intros.
rewrite lseg_neq by auto.
unfold lseg_cons.
apply semax_pre0 with
 (EX h: elemtype ls, EX r: list val, EX y: val,
  !!(s = v :: r /\ is_pointer_or_null y) &&
    PROPx P (LOCALx Q (SEPx (list_token dsh v :: list_cell ls dsh h v ::
       field_at psh list_struct (StructField list_link :: nil)
                   (valinject
                      (nested_field_type list_struct
                         (StructField list_link :: nil)) y) v ::
        lseg ls dsh psh r y v2 :: R)))).
go_lowerx; entailer.
Exists h r y.
entailer!.
Intros h r y.
apply semax_extract_prop; intros [? ?].
eauto.
Qed.


Lemma semax_lseg_nonnull (ls: listspec list_structid list_link list_token):
  forall Espec
      E Delta P Q dsh psh s v R c Post,
    ~ (readable_share dsh) ->
   ENTAIL Delta, PROPx P (LOCALx Q
            (SEPx (lseg ls dsh psh s v nullval :: R))) |--
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list val) (y: val),
    s=v::r -> is_pointer_or_null y ->
    semax(OK_spec := Espec) E Delta
        (PROPx P (LOCALx Q
        (SEPx (list_token dsh v :: list_cell ls dsh h v ::
                  field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) v ::
                  lseg ls dsh psh r y nullval ::
                  R)))) c Post) ->
   semax E Delta
       (PROPx P (LOCALx Q (SEPx (lseg ls dsh psh s v nullval :: R))))
       c Post.
Proof.
intros.
assert_PROP (~ ptr_eq v nullval).
rewrite H0.
normalize.
apply semax_lseg_neq; auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_structid list_link list_token):
    forall dsh psh p q,
   lseg ls dsh psh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 reflexivity.
Qed.

Lemma lseg_cons_eq (ls: listspec list_structid list_link list_token):
     forall dsh psh h r x z ,
     ~ (readable_share dsh) ->
    lseg ls dsh psh (h::r) x z ⊣⊢
        !!(x = h /\ ~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_token dsh x * list_cell ls dsh (vund ls) x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x *
   lseg ls dsh psh r y z).
Proof.
 intros. rewrite lseg_unroll by auto.
 apply pred_ext.
 apply bi.or_elim.
 Intros.
 inv H1.
 unfold lseg_cons.
 Intros h0 r0 y.
 symmetry in H1; inv H1.
 Exists y; entailer!.
 rewrite nonreadable_list_cell_eq; auto.
 rewrite <- bi.or_intro_r.
 Intros y.
 unfold lseg_cons.
 rewrite prop_true_andp by auto.
 Exists (vund ls) r y; entailer!.
Qed.

Definition lseg_cons_right (ls: listspec list_structid list_link list_token)
           dsh psh (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) &&
       EX r:list val , EX y:val,
             !!(l=r++y::nil /\ is_pointer_or_null y)  &&
                       list_cell ls dsh (vund ls) y *
             field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_structid list_link list_token):
      forall dsh psh l x h y w z,
     sepalg.nonidentity psh ->
     ~ (readable_share dsh) ->
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh l x y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls dsh psh (l++y::nil) x z * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) w) z.
Proof.
intros. rename H into SH. rename H0 into NR.
assert (SZ: 0 < sizeof (nested_field_type list_struct (DOT list_link)))
  by (rewrite list_link_type; unfold sizeof; simpl; destruct Archi.ptr64; computable).
rewrite (field_at_isptr _ _ _ _ z).
Intros.
revert x; induction l; simpl; intros.
*
unfold lseg.
simpl.
Intros; subst.
Exists z.
entailer!.
rewrite (nonreadable_list_cell_eq); auto.
*
unfold lseg; simpl.
Intros x0; Exists x0.
iIntros "((H & ? & lseg) & Hz)".
iDestruct (IHl with "[$H $Hz $lseg]") as "?".
iStopProof; entailer!.
auto.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_structid list_link list_token): forall dsh psh l x h y,
     ~ (readable_share dsh) ->
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) nullval) y *
             lseg ls dsh psh l x y
   |--   lseg ls dsh psh (l++y::nil) x nullval.
Proof.
intros. rename H into NR.
unfold lseg.
revert x; induction l; simpl; intros.
*
Intros.
Exists nullval; entailer!.
rewrite nonreadable_list_cell_eq; auto.
*
Intros x0.
Exists x0.
iIntros "(H & ? & lseg)".
iDestruct (IHl with "[$H $lseg]") as "$".
iStopProof; entailer!.
Qed.


Lemma lseg_cons_right_list (ls: listspec list_structid list_link list_token):
      forall dsh psh l l' x h y z,
     sepalg.nonidentity psh ->
     ~ (readable_share dsh) ->
             list_token dsh y * list_cell ls dsh h y * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) z) y *
             lseg ls dsh psh l x y * lseg ls dsh psh l' z nullval
   |--   lseg ls dsh psh (l++y::nil) x z * lseg ls dsh psh l' z nullval.
Proof.
intros.
destruct l'.
rewrite lseg_nil_eq.
Intros; subst.
rewrite prop_true_andp by apply ptr_eq_nullval.
rewrite lseg_cons_right_null; auto.
rewrite lseg_cons_eq; auto.
Intros u. Exists u. subst.
rewrite !prop_true_andp by auto.
iIntros "(H & ((? & ?) & Hv) & ?)".
iDestruct (lseg_cons_right_neq with "[$H $Hv]") as "?"; auto.
iStopProof; cancel.
Qed.

Lemma lseg_unroll_right (ls: listspec list_structid list_link list_token): forall sh sh' l x z ,
    lseg ls sh sh' l x z ⊣⊢ (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh sh' l x z.
Abort.  (* not likely true *)

Lemma lseg_local_facts:
  forall ls dsh psh contents p q,
     lseg ls dsh psh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply bi.pure_elim_l; intro.
unfold ptr_eq in H.
apply bi.pure_intro.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
unfold Int.cmpu in H.
destruct H as [? [? ?]].
apply int_eq_e in H0.
apply int_eq_e in H1. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
unfold Int64.cmpu in H.
destruct H as [? [? ?]].
apply int64_eq_e in H0.
apply int64_eq_e in H1. subst.
split3; auto; done.
destruct q; try contradiction.
destruct H; subst.
unfold Ptrofs.cmpu in H0.
apply ptrofs_eq_e in H0.
subst. tauto.
normalize.
rewrite field_at_isptr.
Intros; entailer!.
split. intro; subst q.
contradiction H. normalize.
intros. discriminate.
Qed.

Definition lseg_cell  (ls: listspec list_structid list_link list_token)
    (dsh psh : share)
    (v: elemtype ls) (x y: val) :=
   !!is_pointer_or_null y && list_token dsh x * list_cell ls dsh v x * field_at psh list_struct (StructField list_link :: nil) (valinject (nested_field_type list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall
  (ls : listspec list_structid list_link list_token) (dsh psh : share) (h : elemtype ls)
   (r : list val )  (x z : val),
     ~ (readable_share dsh) ->
  lseg ls dsh psh (x :: r) x z ⊣⊢
  !!(~ ptr_eq x z) && (EX  y : val, lseg_cell ls dsh psh h x y * lseg ls dsh psh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq by auto.
  unfold lseg_cell.
 normalize.
 f_equiv. intros y.
 f_equiv. f_equiv. tauto. rewrite nonreadable_list_cell_eq; done.
Qed.

Lemma list_append: forall {dsh psh: share}
  {ls : listspec list_structid list_link list_token} (hd mid tl:val) ct1 ct2 P,
  (forall tl', lseg_cell ls dsh psh (vund ls) tl tl' * P tl |-- False) ->
  (lseg ls dsh psh ct1 hd mid) * lseg ls dsh psh ct2 mid tl * P tl|--
  (lseg ls dsh psh (ct1 ++ ct2) hd tl) * P tl.
Proof.
 intros.
 unfold lseg.
 revert hd; induction ct1; simpl; intros; auto.
*
 normalize.
*
 Intros y.
 Exists y.
 apply bi.and_intro.
 +
  destruct (eq_dec hd tl); [|entailer!].
  subst.
  clear IHct1.
  specialize (H y).
  unfold lseg_cell in H.
  iIntros "(((H & ?) & ?) & P)"; iDestruct (H with "[H $P]") as "[]".
  iStopProof; entailer!.
 +
  go_lower.sep_apply IHct1.
  entailer!.
Qed.

Lemma list_append_null:
  forall
   (ls: listspec list_structid list_link list_token)
   (dsh psh: share)
   (hd mid: val) ct1 ct2,
   lseg ls dsh psh ct1 hd mid * lseg ls dsh psh ct2 mid nullval |--
   lseg ls dsh psh (ct1++ct2) hd nullval.
Proof.
intros.
 rewrite <- bi.sep_emp.
 rewrite (list_append _ _ _ _ _ (fun _ => emp)).
 iIntros "($ & _)".
 intros.
  unfold lseg_cell. simpl. saturate_local. destruct H. contradiction H.
Qed.

Lemma list_cell_valid_pointer:
  forall (LS: listspec list_structid list_link list_token) (dsh psh: Share.t) v p,
   sepalg.nonidentity dsh ->
   sepalg.join_sub dsh psh ->
   field_offset cenv_cs list_link list_fields + sizeof (field_type list_link list_fields)
   = field_offset_next cenv_cs list_link list_fields  (co_sizeof (get_co list_structid)) ->
   list_cell LS dsh v p * field_at_ psh list_struct (StructField list_link::nil) p
  |-- valid_pointer p.
Proof.
  intros ? ? ? ? ? NON_ID ? ?.
 destruct H as [bsh ?].
 rewrite <- (field_at__share_join _ _ _ _ _ _ H).
 iIntros "(c & f & _)".
 iCombine "c f" as "d"; rewrite list_cell_link_join_nospacer; auto.
 unfold data_at_, field_at_, data_at.
 iStopProof.
 saturate_local.
 rewrite field_at_valid_ptr; auto.
 2: { change (nested_field_type list_struct nil) with list_struct.
      apply LsegGeneral.sizeof_list_struct_pos. }
 unfold field_address.
 if_tac; auto.
 contradiction.
Qed.

Lemma list_cell_valid_pointerx:
  forall (ls : listspec list_structid list_link list_token)  sh v p,
   sh <> Share.bot ->
   list_cell ls sh v p |-- valid_pointer p.
Proof.
 intros.
 unfold list_cell.
Abort.  (* probably not true; would be true with a direct (non-magic-wand)
      definition of list_cell *)

Lemma lseg_valid_pointer:
  forall (ls : listspec list_structid list_link list_token) dsh psh contents p q R,
   sepalg.nonidentity dsh ->
   dsh <> Share.bot ->
   sepalg.join_sub dsh psh ->
   field_offset cenv_cs list_link list_fields + sizeof (field_type list_link list_fields)
   = field_offset_next cenv_cs list_link list_fields  (co_sizeof (get_co list_structid)) ->
    (R |-- valid_pointer q) ->
    R * lseg ls dsh psh contents p q |-- valid_pointer p.
Proof.
intros.
destruct contents.
rewrite lseg_nil_eq, H3. entailer!.
unfold lseg; simpl.
Intros y.
iIntros "(? & ((? & cell) & Hp) & ?)".
iPoseProof (list_cell_valid_pointer with "[$cell Hp]") as "$"; eauto.
iStopProof; cancel.
Qed.

End LIST2.

Lemma join_sub_Tsh:
  forall sh, sepalg.join_sub sh Tsh.
Admitted. (* easy *)
#[export] Hint Resolve join_sub_Tsh: valid_pointer.

#[export] Hint Rewrite @lseg_nil_eq : norm.

#[export] Hint Rewrite @lseg_eq using reflexivity: norm.

#[export] Hint Resolve lseg_local_facts : saturate_local.

#[export] Hint Resolve denote_tc_test_eq_split : valid_pointer.

Ltac resolve_lseg_valid_pointer :=
match goal with
 | |- ?Q |-- valid_pointer ?p =>
   match Q with context [lseg ?A ?B ?C ?D p ?q] =>
   repeat rewrite bi.sep_assoc;
   pull_right (lseg A B C D p q);
   apply lseg_valid_pointer; [auto | | | reflexivity | ];
   auto 50 with valid_pointer
   end
 end.

#[export] Hint Extern 10 (_ |-- valid_pointer _) =>
       resolve_lseg_valid_pointer : valid_pointer.

Ltac resolve_list_cell_valid_pointer :=
 match goal with |- ?A |-- valid_pointer ?p =>
  match A with context [@list_cell ?cs ?sid ?lid ?tok ?LS ?dsh ?v p] =>
   match A with context [field_at ?psh ?t (StructField lid::nil) ?v' p] =>
    trans
      (@list_cell cs sid lid tok LS dsh v p *
      field_at_ psh t (StructField lid::nil) p * True);
      [cancel
      | apply sepcon_valid_pointer1;
        apply list_cell_valid_pointer; [auto | | reflexivity]; auto with valid_pointer]
   end
  end
 end.

#[export] Hint Extern 10 (_ |-- valid_pointer _) =>
   resolve_list_cell_valid_pointer : valid_pointer.

End Links.

Arguments elemtype {cs} {list_structid} {list_link} {list_token} ls / .
