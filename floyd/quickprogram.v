Require Import VST.veric.base VST.veric.Cop2.
Require Import compcert.cfrontend.Ctypes.

Module QP.


Record composite : Type := {
  co_su: struct_or_union;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
}.

Definition composite_env : Type := PTree.t composite.

Record program (F: Type) : Type := {
  prog_defs: PTree.t (globdef (fundef F) type);
  prog_public: list ident;
  prog_main: ident;
  prog_comp_env: composite_env
}.

Arguments prog_defs {F} _.
Arguments prog_public {F} _.
Arguments prog_main {F} _.
Arguments prog_comp_env {F} _.
End QP.

Definition QPcomposite_of_composite (c: composite) :=
 {| QP.co_su := c.(co_su);
    QP.co_members := c.(co_members);
    QP.co_attr := c.(co_attr);
    QP.co_sizeof := c.(co_sizeof);
    QP.co_alignof := c.(co_alignof);
    QP.co_rank := c.(co_rank)
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

Definition QPcomposite_env_of_composite_env :
     composite_env -> QP.composite_env :=
 PTree.map1 QPcomposite_of_composite.

Definition PTree_Forall {A: Type} (F: A -> Prop) (m: PTree.t A): Prop :=
  forall i, match PTree.get i m with Some c => F c | None => True end.

Definition QPcomposite_env_OK: QP.composite_env -> Prop :=
  PTree_Forall QPcomposite_OK.

Lemma QPcomposite_of_composite_OK: 
  forall c, QPcomposite_OK (QPcomposite_of_composite c).
Proof.
intros.
split3; simpl.
apply co_sizeof_pos.
apply co_alignof_two_p.
apply co_sizeof_alignof.
Qed.

Lemma QPcomposite_env_of_composite_env_OK:
  forall (ce: composite_env), 
    QPcomposite_env_OK (QPcomposite_env_of_composite_env ce).
Proof.
intros. intro i.
unfold QPcomposite_env_of_composite_env.
rewrite PTree.gmap1.
destruct ( ce ! i) eqn:?H; simpl; auto.
apply QPcomposite_of_composite_OK.
Qed.


Lemma PTree_Forall_elements:
 forall A (F: A -> Prop) (m: PTree.t A),
  PTree_Forall F m <-> Forall (fun ix => F (snd ix)) (PTree.elements m).
Proof.
intros.
split; intros.
-
red in H.
apply Forall_forall.
intros (i,y) ?.
simpl.
specialize (H i).
apply PTree.elements_complete in H0.
rewrite H0 in H.
auto.
-
intro i.
rewrite -> Forall_forall in H.
destruct (m ! i) eqn:?H; auto.
specialize (H (i,a)).
apply H.
apply PTree.elements_correct.
auto.
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

Definition composite_env_of_QPcomposite_env
   (ce: QP.composite_env)
   (H: QPcomposite_env_OK ce) : composite_env :=
 PTree_Properties.of_list
   (QP_list_helper _ (proj1 (PTree_Forall_elements _ _ _) H)).

Lemma PTree_elements_map1:
  forall {A B} (f: A -> B)  e, PTree.elements (PTree.map1 f e) =
                  map (fun ix => (fst ix, f (snd ix))) (PTree.elements e).
Proof.
intros.
unfold PTree.elements.
set (g := (fun ix : positive * A => (fst ix, f (snd ix)))).
change (@nil (positive * B)) with (map g (@nil (positive * A))).
forget (@nil (positive * A)) as r.
forget 1%positive as n.
revert r n.
induction e; intros.
simpl. auto.
simpl.
destruct o; simpl.
rewrite IHe2.
rewrite <- IHe1.
simpl.
reflexivity.
rewrite IHe2.
rewrite <- IHe1.
simpl.
reflexivity.
Qed.


Lemma composite_of_QPcomposite_of_composite:
  forall c H, composite_of_QPcomposite (QPcomposite_of_composite c) H = c.
Proof.
intros.
destruct c; simpl.
unfold composite_of_QPcomposite.
f_equal; simpl; auto; apply proof_irr.
Qed.


Lemma QPcomposite_of_composite_of_QPcomposite:
  forall c H, QPcomposite_of_composite (composite_of_QPcomposite c H) = c.
Proof.
intros.
destruct c; simpl.
unfold composite_of_QPcomposite.
f_equal; simpl; auto; apply proof_irr.
Qed.

Lemma composite_env_of_QPcomposite_env_of_composite_env:
 forall (ce: composite_env) OK,
 forall i,
  PTree.get i 
   (composite_env_of_QPcomposite_env
    (QPcomposite_env_of_composite_env ce) OK) =
  PTree.get i ce.
Proof.
intros.
unfold composite_env_of_QPcomposite_env.
destruct (ce ! i) eqn:?H.
-
destruct (PTree_Properties.of_list_dom (PTree.elements ce) i).
change i with (fst (i,c)).
apply in_map.
apply PTree.elements_correct; auto.
assert (x=c) by (rewrite PTree_Properties.of_list_elements in H0; congruence).
subst x.
unfold QPcomposite_env_of_composite_env.
set (j := proj1 _ _).
clearbody j.
pose proof (PTree_elements_map1 QPcomposite_of_composite ce).
assert (Forall
      (fun ix : positive * QP.composite =>
       QPcomposite_OK (snd ix)) (map  (fun ix : positive * composite =>
        (fst ix, QPcomposite_of_composite (snd ix)))
       (PTree.elements ce))).
rewrite H1 in j; auto.
assert
 ((PTree_Properties.of_list (QP_list_helper _ H2)) ! i = Some c).
2:{
rewrite <- H3.
f_equal.
f_equal.
apply QP_list_helper_ext; auto.
}
clear j H1 H0.
pose proof (PTree.elements_correct ce i H).
pose proof (PTree.elements_keys_norepet ce).
set (al := PTree.elements ce) in *.
clearbody al.
clear ce H OK.
generalize H2; intro H2'.
rewrite -> Forall_forall in H2.
specialize (H2 (i, QPcomposite_of_composite c)).
spec H2.
change (i, QPcomposite_of_composite c)
 with ( (fun ix : positive * composite =>
      (fst ix, QPcomposite_of_composite (snd ix))) (i,c)).
apply in_map; auto.
simpl in H2.
apply PTree_Properties.of_list_norepet.
+
replace (map fst _) with (map fst al); auto.
clear.
induction al. auto.
simpl. f_equal; auto.
+
induction al.
inv H0.
destruct H0.
subst a.
simpl. left.
rewrite composite_of_QPcomposite_of_composite.
auto.
inv H1.
right.
apply IHal; auto.
-
match goal with |- ?A = _ => destruct A eqn:?H; auto end.
elimtype False.
apply PTree_Properties.in_of_list in H0.
assert (~ In i (map fst (PTree.elements ce))).
intro.
apply list_in_map_inv in H1.
destruct H1 as [[j d] [? ?]].
simpl in H1; subst j.
apply PTree.elements_complete in H2.
congruence.
apply H1; clear H1 H.
unfold QPcomposite_env_of_composite_env in H0.
apply (in_map fst) in H0.
simpl in H0.
match goal with H: In _ ?a |- In _ ?b => replace b with a; auto end.
clear.
set (H := proj1 _ _).
clearbody H.
assert (Forall (fun ix : positive * QP.composite => QPcomposite_OK (snd ix))
 (map (fun ix => (fst ix, QPcomposite_of_composite (snd ix))) (PTree.elements ce))).
rewrite PTree_elements_map1 in H.
auto.
transitivity 
 (map fst
   (QP_list_helper _ H0)).
f_equal.
apply QP_list_helper_ext; auto.
apply PTree_elements_map1.
clear.
induction (PTree.elements ce).
reflexivity.
simpl; f_equal; auto.
Qed.

Lemma QPcomposite_env_of_composite_env_of_QPcomposite_env:
 forall (ce: QP.composite_env)  (H : QPcomposite_env_OK ce),
 forall i,
  PTree.get i 
   (QPcomposite_env_of_composite_env
    (composite_env_of_QPcomposite_env ce H)) =
  PTree.get i ce.
Proof.
intros.
unfold QPcomposite_env_of_composite_env.
rewrite PTree.gmap1.
unfold composite_env_of_QPcomposite_env.
forget (proj1 (PTree_Forall_elements QP.composite QPcomposite_OK ce) H) as H0.
rewrite <- (PTree_Properties.of_list_elements ce).
pose proof (PTree.elements_keys_norepet ce).
clear H. pose proof I.
induction (PTree.elements ce).
simpl. unfold option_map.
unfold PTree_Properties.of_list; simpl.
rewrite !PTree.gempty.
auto.
pose proof (Forall_inv_tail H0).
pose proof (Forall_inv H0).
inv H1.
specialize (IHl H2 H7).
destruct a as [j d].
simpl in *.
unfold option_map.
destruct (ident_eq i j).
subst j.
pose proof (PTree_Properties.of_list_unique i d nil l H6).
simpl in H1.
etransitivity.
2: symmetry; apply H1.
pose proof (PTree_Properties.of_list_unique i 
    (composite_of_QPcomposite d (Forall_inv H0)) nil
    (QP_list_helper l (Forall_inv_tail H0))).
simpl in H4.
set (x := (PTree_Properties.of_list
        ((i, composite_of_QPcomposite d (Forall_inv H0))
         :: QP_list_helper l (Forall_inv_tail H0))) ! i) in *.
change ((PTree_Properties.of_list
        ((i, composite_of_QPcomposite d (Forall_inv H0))
         :: QP_list_helper l (Forall_inv_tail H0))) ! i ) with x in H4.
rewrite H4.
rewrite QPcomposite_of_composite_of_QPcomposite.
auto.
clear - H6.
contradict H6.
set (H := Forall_inv_tail H0) in *.
clearbody H; clear H0.
induction l; simpl; auto.
destruct a as [j c].
simpl.
simpl in H6.
destruct H6; auto; right.
specialize (IHl (Forall_inv_tail H)).
auto.
unfold option_map in IHl.
destruct ( (PTree_Properties.of_list (QP_list_helper l H2)) ! i) eqn:?H.
+
rewrite (PTree_Properties.of_list_norepet ((j,d)::l) i (QPcomposite_of_composite c)).
rewrite (PTree_Properties.of_list_norepet
        ( (j, composite_of_QPcomposite d (Forall_inv H0)) :: 
          QP_list_helper l (Forall_inv_tail H0)) i c).
auto.
simpl.
constructor; auto.
clear H.
forget (Forall_inv_tail H0) as H.
clear - H6.
contradict H6.
induction l as [ | [? ?]]; simpl in *; auto.
destruct H6; auto; right.
apply (IHl (Forall_inv_tail H)); auto.
clear H.
forget (Forall_inv_tail H0) as H.
clear - H7.
induction l as [ | [? ?]].
constructor.
simpl  in *.
inv H7.
constructor; auto.
contradict H2.
forget (Forall_inv_tail H) as H'.
clear - H2.
induction l as [ | [? ?]].
inv H2.
simpl in *.
destruct H2; auto; right.
apply (IHl  (Forall_inv_tail H')); auto.
right.
replace (Forall_inv_tail H0) with H2 by (apply proof_irr).
apply PTree_Properties.in_of_list in H1. auto.
constructor; auto.
right.
symmetry in IHl.
apply PTree_Properties.in_of_list; auto.
+
destruct (  (PTree_Properties.of_list
     ((j, composite_of_QPcomposite d (Forall_inv H0))
      :: QP_list_helper l (Forall_inv_tail H0))) ! i) eqn:?H.
symmetry.
apply PTree_Properties.in_of_list in H4.
destruct H4.
congruence.
destruct (PTree_Properties.of_list_dom (QP_list_helper l (Forall_inv_tail H0)) i).
apply (in_map fst) in H4; auto.
replace (Forall_inv_tail H0) with H2 in H5 by (apply proof_irr).
congruence.
symmetry.
destruct ((PTree_Properties.of_list ((j, d) :: l)) ! i) eqn:?H; auto.
elimtype False.
apply PTree_Properties.in_of_list in H5.
destruct H5. congruence.
symmetry in IHl.
destruct (PTree_Properties.of_list_dom l i).
apply (in_map fst) in H5; auto.
congruence.
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

Definition program_of_QPprogram {F} (p: QP.program F) 
   : Errors.res (Ctypes.program F) :=
 let defs := PTree.elements p.(QP.prog_defs) in
 let public := p.(QP.prog_public) in
 let main := p.(QP.prog_main) in
 let types := map compdef_of_compenv_element 
                             (sort_rank (PTree.elements (p.(QP.prog_comp_env))) nil) in
 make_program types defs public main.

Definition QPprogram_of_program {F} (p: Ctypes.program F) : QP.program F :=
 {| QP.prog_defs := PTree_Properties.of_list p.(prog_defs);
   QP.prog_public := p.(prog_public);
   QP.prog_main := p.(prog_main);
   QP.prog_comp_env := QPcomposite_env_of_composite_env p.(prog_comp_env)
 |}.

Import ListNotations.


Definition merge_PTrees {X} (merge: X -> X -> Errors.res X) (a b: PTree.t X) : Errors.res (PTree.t X) :=
  PTree.fold  (fun m i y =>
          match m with Errors.Error _ => m
          | Errors.OK m' =>
                match PTree.get i m' with
                 | Some x => match merge x y with
                                       | Errors.Error e => Errors.Error e
                                       | Errors.OK xy => Errors.OK (PTree.set i xy m')
                                       end
                 | None => Errors.OK (PTree.set i y m')
                 end
           end) a (Errors.OK b).


Definition merge_disjoint_PTrees {X} (a b: PTree.t X) : Errors.res (PTree.t X) :=
  PTree.fold  (fun m i y =>
                      match m with Errors.Error _ => m
                      | Errors.OK m' => match PTree.get i m' with
                                             | Some _ => Errors.Error [Errors.MSG "nondisjoint PTrees: identifier="%string; Errors.POS i]
                                             | None => Errors.OK (PTree.set i y m')
                                             end
                      end) a (Errors.OK b).

Definition merge_consistent_PTrees {X} (eqb: X -> X -> bool) (a b: PTree.t X) 
      : Errors.res (PTree.t X) :=
  PTree.fold  (fun m i y =>
                      match m with Errors.Error _ => m
                      | Errors.OK m' => match PTree.get i m' with
                                             | Some x => 
                                                 if eqb x y then Errors.OK m' 
                                                 else Errors.Error [Errors.MSG "inconsistent PTrees at identifier="; Errors.POS i]
                                             | None => Errors.OK (PTree.set i y m')
                                             end
                      end) a (Errors.OK b).

Definition QPcomposite_eq (c d: QP.composite) : bool :=
 (eqb_su c.(QP.co_su) d.(QP.co_su) 
 && eqb_list eqb_member c.(QP.co_members) d.(QP.co_members)
 && eqb_attr c.(QP.co_attr) d.(QP.co_attr)
 && Z.eqb c.(QP.co_sizeof) d.(QP.co_sizeof)
 && Z.eqb c.(QP.co_alignof) d.(QP.co_alignof)
 && Nat.eqb c.(QP.co_rank) d.(QP.co_rank))%bool.

Require VST.floyd.linking.

Definition QPlink_progs (p1 p2: QP.program Clight.function) : Errors.res (QP.program Clight.function) :=
 match merge_PTrees linking.merge_globdef (p1.(QP.prog_defs)) p2.(QP.prog_defs) with
 | Errors.Error m => Errors.Error m
 | Errors.OK defs => match merge_consistent_PTrees QPcomposite_eq
                p1.(QP.prog_comp_env) p2.(QP.prog_comp_env)
   with Errors.Error m => Errors.Error m
     | Errors.OK ce => 
   if eqb_ident p1.(QP.prog_main) p2.(QP.prog_main) then
    Errors.OK 
    {| QP.prog_defs := defs;
       QP.prog_public := p1.(QP.prog_public);
       QP.prog_main := p1.(QP.prog_main);
       QP.prog_comp_env := ce
     |}
   else Errors.Error [Errors.MSG "QPlink_progs disagreement on main:";
                               Errors.POS p1.(QP.prog_main);
                               Errors.POS p2.(QP.prog_main)]
 end end.

Module Junkyard.

Fixpoint QPcomplete_type (env : QP.composite_env) (t : type) :  bool :=
  match t with
  | Tarray t' _ _ => QPcomplete_type env t'
  | Tvoid | Tfunction _ _ _ => false
  | Tstruct id _ | Tunion id _ =>
      match env ! id with
      | Some _ => true
      | None => false
      end
  | _ => true
  end.

Fixpoint QPcomplete_members (e: QP.composite_env) (m: members) :=
 match m with
 | nil => true
 | (_,t)::m' => QPcomplete_type e t && QPcomplete_members e m'
 end.

Definition QPcomposite_env_complete (e: QP.composite_env) : Prop :=
  PTree_Forall (fun c => QPcomplete_members e (QP.co_members c) = true) e.

Lemma build_composite_env_helper :
 forall ce
  (H: QPcomposite_env_OK ce)
(*  (Hcomplete: QPcomposite_env_complete ce) *),
  build_composite_env
    (map compdef_of_compenv_element
       (PTree.elements ce)) =
  Errors.OK
    (composite_env_of_QPcomposite_env ce H).
Proof.
intros.
red in H.
unfold composite_env_of_QPcomposite_env.
set (H0 := proj1 _ _).
clearbody H0.
(*red in Hcomplete.
rewrite PTree_Forall_elements in Hcomplete.
*)
pose proof (PTree.elements_keys_norepet ce).
forget (PTree.elements ce) as al.
clear H ce.
unfold build_composite_env.
unfold PTree_Properties.of_list.
assert (forall i, In i (map fst al) -> (PTree.empty composite) ! i = None).
intros. apply PTree.gempty.
forget (PTree.empty composite) as e.
revert e H; induction al as [ | [i c]]; simpl; intros; auto.
inv H1.
unfold Errors.bind.
unfold composite_of_def.
rewrite H by auto.
Abort.

(*
Definition program_of_QPprogram {F} (p: QP.program F) 
  (H: QPcomposite_env_OK (p.(QP.prog_comp_env)))
  (H0: QPcomposite_env_complete (p.(QP.prog_comp_env)))
   : Ctypes.program F  :=
 {| prog_defs := PTree.elements p.(QP.prog_defs);
    prog_public := p.(QP.prog_public);
    prog_main := p.(QP.prog_main);
    prog_types := map compdef_of_compenv_element 
                             (sort_rank (PTree.elements (p.(QP.prog_comp_env))) nil);
    prog_comp_env := composite_env_of_QPcomposite_env p.(QP.prog_comp_env) H;
    prog_comp_env_eq := 8 
 |}.
*)

End Junkyard.
















