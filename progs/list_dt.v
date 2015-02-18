(* Require Import floyd.proofauto.
   TEMPORARILY replace "floyd.proofauto" 
   with all the imports in the list below.
   This reduces makefile-based recompilation
   when changing things in (e.g.) forward.v
*)
Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.type_id_env.
Require Import floyd.efield_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.rangespec_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.nested_field_re_lemmas.
Require Import floyd.nested_loadstore.
Require Import floyd.unfold_data_at.
Require Import floyd.entailer.
(*  End TEMPORARILY *)

Local Open Scope logic.

Class listspec (list_struct: type) (list_link: ident) :=
  mk_listspec {  
   list_fields: fieldlist;
   list_structid: ident;
   list_struct_eq: list_struct= Tstruct list_structid list_fields noattr;
   list_struct_alignas_legal: legal_alignas_type list_struct = true;
   list_link_type: nested_field_type2 list_struct (StructField list_link :: nil) = Tcomp_ptr list_structid noattr
}.

Section LIST.
Context  {list_struct: type} {list_link: ident}.

Definition links' (ls: listspec list_struct list_link) (sh: share) := 
  HORec (fun (R: (list val)*(val*val) -> mpred) (lp: (list val)*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (h=first /\ ~ (ptr_eq first last)) && 
                        EX tail:val, 
                           !! (is_pointer_or_null tail) &&
                           field_at sh list_struct (StructField list_link::nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) first
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Definition links (ls: listspec list_struct list_link) (sh: share) (contents: list val) (x y: val) : mpred :=
  links' ls sh (contents,(x,y)).

Lemma links_unfold (ls: listspec list_struct list_link): forall sh contents v1 v2,
  links ls sh contents v1 v2 = 
  match contents with
  | h::t => !!(h=v1 /\ ~ptr_eq v1 v2) && EX tail: val, 
                           !! (is_pointer_or_null tail) &&
                           field_at sh list_struct (StructField list_link::nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) v1
                           * |> links ls sh t tail v2
  | nil => !! (ptr_eq v1 v2) && emp
 end.
Proof.
 intros. unfold links.
 unfold links' at 1. rewrite HORec_fold_unfold; auto.
 apply prove_HOcontractive; intros.
 destruct x. destruct l. 
 auto 50 with contractive.
 destruct p.
 auto 50 with contractive.
Qed.

Lemma links_eq (ls: listspec list_struct list_link):
  forall sh l v , 
  is_pointer_or_null v ->
    links ls sh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (links_unfold ls sh l v v).
destruct l.
f_equal. f_equal.
unfold ptr_eq.
unfold typecheck_val in H.
destruct v; inv H; unfold Int.cmpu; rewrite Int.eq_true; auto;
 apply prop_ext; intuition.
apply pred_ext; repeat (apply derives_extract_prop; intro).
destruct H0. contradiction H1. destruct v; inv H; simpl; rewrite Int.eq_true; auto.
inv H0.
Qed.

Definition links_cons (ls: listspec list_struct list_link) sh (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX r:list val, EX y:val, 
             !!(l=x::r  /\ is_pointer_or_null y) && 
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x * 
             |> links ls sh r y z.

Lemma links_neq (ls: listspec list_struct list_link):  forall sh l x z , 
  is_pointer_or_null x ->
  is_pointer_or_null z ->
  ptr_neq x z -> 
    links ls sh l x z = links_cons ls sh l x z.
Proof.
unfold links_cons, ptr_neq; intros.
rewrite links_unfold at 1; auto.
destruct l.
apply pred_ext; apply derives_extract_prop; intro.
contradiction. clear H2.
apply exp_left; intro r.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H2.
apply pred_ext; apply derives_extract_prop; intro.
destruct H2 as [? _]. subst x.
apply exp_left; intro tail.
apply andp_right; try apply prop_right; auto.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'; apply andp_right.
normalize.
normalize.
apply exp_left; intro r'.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H3.
apply andp_right.
apply prop_right; auto.
apply exp_right with y.
normalize.
Qed.

Lemma links_unroll (ls: listspec list_struct list_link): forall sh l x z , 
    links ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || links_cons ls sh l x z.
Proof.
intros.
rewrite links_unfold at 1.
apply pred_ext; destruct l.
apply derives_extract_prop; intro.
repeat rewrite prop_true_andp by auto.
apply orp_right1; auto.
apply orp_right2.
unfold links_cons.
apply derives_extract_prop; intros [? ?].
apply exp_left; intro tail.
subst x.
normalize.
apply exp_right with l.
rewrite TT_andp.
apply exp_right with tail.
normalize.
apply orp_left.
rewrite andp_assoc.
repeat (apply derives_extract_prop; intro).
rewrite prop_true_andp by auto; auto.
unfold links_cons.
apply derives_extract_prop; intro.
apply exp_left; intro r.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H0.
apply orp_left.
rewrite andp_assoc.
repeat (apply derives_extract_prop; intro).
inv H0.
unfold links_cons.
apply derives_extract_prop; intro.
apply exp_left; intro r.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
symmetry in H0; inv H0.
rewrite prop_true_andp by auto.
apply exp_right with y.
normalize.
Qed.

Lemma links_nonnull (ls: listspec list_struct list_link):
  forall sh s v,
      typed_true (tptr list_struct) v ->
     links ls sh s v nullval = links_cons ls sh s v nullval.
Proof.
intros. subst. 
rewrite links_unroll.
rewrite andp_assoc.
apply pred_ext.
apply orp_left; auto.
repeat (apply derives_extract_prop; intro).
subst.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
destruct H0.
rewrite H0 in H. inv H.
apply orp_right2. auto.
Qed.

Lemma links_nil_eq (ls: listspec list_struct list_link): 
    forall sh p q, links ls sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite links_unroll.
rewrite andp_assoc.
 apply pred_ext.
 apply orp_left.
repeat (apply derives_extract_prop; intro).
rewrite prop_true_andp by auto; auto.
 unfold links_cons.
apply derives_extract_prop; intro.
 apply exp_left; intro r.
 apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
 inv H0.
apply derives_extract_prop; intro.
repeat rewrite prop_true_andp by auto.
 apply orp_right1. auto.
Qed.

Lemma links_cons_eq (ls: listspec list_struct list_link):
     forall sh h r x z , 
    links ls sh (h::r) x z = 
        !!(h=x /\ ~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x *
   |>links ls sh r y z).
Proof.
 intros. rewrite links_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H0.
 unfold links_cons.
 apply derives_extract_prop; intro.
 apply exp_left; intro r0.
 apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
 inv H0.
 rewrite prop_true_andp by auto.
 apply exp_right with y.
 rewrite prop_true_andp by auto.
 auto.
 apply derives_extract_prop; intros [? ?]. subst x.
 apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intro.
 apply orp_right2.
 unfold links_cons.
 rewrite prop_true_andp by auto.
 apply exp_right with r.
 apply exp_right with y.
 rewrite prop_true_andp by auto.
 auto.
Qed.

Lemma eqp_e {A} {NA: NatDed A}{IA: Indir A}{RA: RecIndir A}:
  forall (P Q : A), (TT |-- P <=> Q) -> P=Q.
Proof.
intros.
apply pred_ext;
(apply subp_e; eapply derives_trans; [apply H | apply fash_derives]).
apply andp_left1; auto.
apply andp_left2; auto.
Qed.

Lemma eqp_i1 {A} {NA: NatDed A}{IA: Indir A}{RA: RecIndir A}:
  forall P (Q R : A),
     unfash P && Q |-- R ->
     unfash P && R |-- Q ->
    P |-- Q <=> R.
Proof.
 intros.
 rewrite fash_andp; apply andp_right; apply subp_i1; auto.
Qed.

Lemma ptr_eq_dec:
  forall x z, {ptr_eq x z}+{~ptr_eq x z}.
Proof.
unfold ptr_eq; intros.
destruct x; simpl; auto. destruct z; simpl; auto. destruct (Int.eq i i0); auto;
destruct (Int.eq i (Int.repr 0)); simpl; auto; intuition. 
destruct z; auto. destruct (eq_dec b b0).
subst. destruct (Int.eq i i0); auto. right; intros [? ?]; auto. inv H0.
right; intros [? ?]. contradiction.
Qed.

Lemma list_last: forall {A} (l: list A),
   l=nil \/ exists prefix, exists y, l = prefix ++ y :: nil.
Proof.
induction l.
left; auto.
right.
destruct IHl as [? | [prefix [y ?]]].
subst. exists nil, a; auto.
subst. exists (a::prefix), y; auto.
Qed.


Lemma allp_andp1  {A}{ND: NatDed A}:  forall B (any: B) (p: B -> A) q, andp (allp p) q = (allp (fun x => andp (p x) q)).
Proof.
 intros. apply pred_ext.
 apply allp_right; intro x.
 apply andp_derives; auto. apply allp_left with x; auto.
 apply andp_right. apply allp_right; intro x. apply allp_left with x. apply andp_left1; auto.
 apply allp_left with any. apply andp_left2; auto.
Qed.

Lemma allp_andp2  {A}{ND: NatDed A}:  forall B (any: B) p (q: B -> A), 
     andp p (allp q) = (allp (fun x => andp p (q x))).
Proof.
intros. rewrite andp_comm. rewrite allp_andp1; auto.
f_equal. extensionality x. rewrite andp_comm; auto.
Qed.

Lemma links_cons_right_null (ls: listspec list_struct list_link): forall sh l x y, 
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * 
             links ls sh l x y
   |--   links ls sh (l++y::nil) x nullval.
Proof.
intros.
assert (TT |-- ALL l: list val, ALL x: val,
                   (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * links ls sh l x y)  
                     >=> links ls sh (l++y::nil) x nullval).
Focus 2.
apply subp_e; eapply derives_trans; [apply H | apply allp_left with l; apply allp_left with x; auto].
clear x l.
apply loeb.
apply allp_right; intro l.
apply allp_right; intro x.
destruct l.
rewrite links_nil_eq.
apply derives_trans with TT; auto.
apply subp_i1.
apply andp_left2.
rewrite sepcon_andp_prop.
apply derives_extract_prop; intro.
rewrite sepcon_emp.
simpl.
apply ptr_eq_e in H. subst y.
rewrite field_at_isptr.
apply derives_extract_prop; intro.
rewrite links_cons_eq.
apply andp_right.  apply prop_right; auto.
split; auto. intro. apply ptr_eq_e in H0. subst. apply H.
apply exp_right with nullval.
rewrite prop_true_andp by (simpl; auto).
rewrite links_nil_eq.
rewrite prop_true_andp. 
apply derives_trans with (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) x * emp).
rewrite sepcon_emp; auto.
apply sepcon_derives; auto.
apply now_later.
simpl. auto.
apply subp_i1.
simpl app.
rewrite links_cons_eq.
rewrite links_cons_eq.
autorewrite with norm. repeat rewrite prop_and; autorewrite with norm.
apply exp_left; intro z.
apply exp_right with z.
repeat rewrite sepcon_andp_prop'.
rewrite andp_comm. rewrite andp_assoc.
rewrite sepcon_comm.
repeat rewrite andp_assoc.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
subst v.
apply andp_right. apply prop_right; auto.
rewrite field_at_isptr.
normalize.
apply andp_right. apply prop_right; repeat split; auto.
intro. apply ptr_eq_e in H. subst; apply Px.
rewrite sepcon_assoc.
rewrite andp_comm.
rewrite unfash_sepcon_distrib.
apply sepcon_derives.
apply andp_left2; auto.
rewrite <- later_unfash.
eapply derives_trans.
apply andp_derives; [apply derives_refl | ].
apply sepcon_derives; [apply derives_refl | apply now_later].
rewrite <- later_sepcon. rewrite <- later_andp.
apply later_derives.
rewrite unfash_allp.
rewrite allp_andp1 by apply nil. apply allp_left with l.
rewrite unfash_allp. rewrite allp_andp1 by apply Vundef. apply allp_left with z.
destruct l.
simpl.
rewrite links_nil_eq.
apply andp_left2.
repeat rewrite sepcon_andp_prop'.
apply derives_extract_prop; intro.
rewrite emp_sepcon.
apply ptr_eq_e in H. subst z.
rewrite links_cons_eq.
rewrite field_at_isptr.
apply derives_extract_prop; intro.
rewrite prop_true_andp.
2: split; auto; intro Hx; destruct y; inv H; inv Hx.
apply exp_right with nullval.
rewrite prop_true_andp by (simpl; auto).
rewrite links_nil_eq.
rewrite prop_true_andp.
eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl | apply now_later]].
rewrite sepcon_emp; auto.
simpl. auto.
eapply derives_trans.
apply andp_derives; [apply unfash_fash | apply derives_refl].
rewrite andp_comm.
apply derives_trans
 with ((field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y *  links ls sh (v::l) z y ) &&
   (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y *  links ls sh (v::l) z y 
     --> links ls sh ((v::l) ++ y :: nil) z nullval)).
2: apply modus_ponens.
apply andp_derives; auto.
rewrite sepcon_comm.
auto.
Qed.

Lemma ptr_eq_refl: forall x, isptr x -> ptr_eq x x.
Proof.
destruct x; simpl; intros; try contradiction.
split; auto. apply Int.eq_true.
Qed.

(*
Lemma links_cons_right_null' (ls: listspec list_struct list_link): forall sh l x y, 
     links ls sh (l++y::nil) x nullval
    |-- links ls sh l x y * |> field_at sh list_struct list_link y nullval.
Proof.
(* Not provable.  The subtle reason is:
  If l<>nil, cannot prove that x<>y.
  One can prove that later-later-later, x<>y, but not now x<>y.
*)
Abort.
*)

Lemma another_ewand_TT_lemma:
 forall A B C: mpred, A && ewand C TT >=> B && ewand C TT |-- A*C >=> B*C.
Admitted.

Lemma list_link_size_in_range (ls: listspec list_struct list_link):  
  0 < sizeof (nested_field_type2 list_struct (StructField list_link :: nil)) < Int.modulus.
Proof.
  rewrite list_link_type.
  cbv.
  split; reflexivity.
Qed.

Lemma uncompomized_valinject_repinject: forall e t (v : reptype t),
  type_is_by_value (uncompomize e t) = true -> valinject t (repinject t v) = v.
Proof.
  intros.
  destruct t; try inversion H; reflexivity.
Qed.

Lemma links_cons_right (ls: listspec list_struct list_link): forall (sh : Share.t) 
         (l : list val) (x y z: val) w,
       field_at sh list_struct (StructField list_link :: nil)
         (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y *
       field_at sh list_struct (StructField list_link :: nil)
         w z *
       links ls sh l x y
       |-- links ls sh (l ++ y :: nil) x z *
           field_at sh list_struct (StructField list_link :: nil)
             w z.
Proof.
intros.
assert (type_is_by_value
        (uncompomize (PTree.empty type)
           (nested_field_type2 list_struct (StructField list_link :: nil))) = true).
  rewrite list_link_type; simpl; auto.
pose proof uncompomized_valinject_repinject (PTree.empty _) (nested_field_type2 list_struct (StructField list_link :: nil)) w H.
remember (repinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) as w'.
subst w.
clear H Heqw'.
rename w' into w.
rewrite (field_at_isptr _ _ _ _ z).
normalize.
assert (TT |-- ALL l: list val, ALL x: val,
                   (((field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y) * links ls sh l x y)  
                          && (ewand (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z) TT))
                     >=> (links ls sh (l++y::nil) x z 
                                 && (ewand (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z) TT))).
Focus 2.
apply subp_e; eapply derives_trans;
   [apply H | apply allp_left with l; apply allp_left with x; auto].
forget (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y) as A.
forget (links ls sh (l ++ y :: nil) x z) as B.
forget (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z) as C.
forget (links ls sh l x y) as D.
rewrite (sepcon_assoc). rewrite (sepcon_comm C). rewrite <- sepcon_assoc.
apply another_ewand_TT_lemma.
clear x l.
apply loeb.
apply allp_right; intro l.
apply allp_right; intro x.
destruct l.
rewrite links_nil_eq.
apply derives_trans with TT; auto.
apply subp_i1.
apply andp_left2.
rewrite sepcon_andp_prop.
rewrite andp_assoc.
apply derives_extract_prop; intro.
rewrite sepcon_emp.
simpl.
apply ptr_eq_e in H; subst y.
rewrite field_at_isptr.
rewrite andp_assoc.
apply derives_extract_prop; intro.
rewrite links_cons_eq.
apply andp_right; [ | apply andp_left2; auto].
apply andp_right.
rewrite prop_and; rewrite prop_true_andp by auto.
apply not_prop_right; intro. apply ptr_eq_e in H0; subst z.
apply ewand_conflict.
eapply derives_trans; [apply sepcon_derives | apply field_at__conflict];
  try apply field_at_field_at_;try apply list_struct_alignas_legal;
  try apply (list_link_size_in_range ls).
apply exp_right with z.
normalize.
rewrite links_nil_eq.
rewrite prop_true_andp by (destruct z; try contradiction; simpl; auto).
apply andp_left1.
apply derives_trans with (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) x * emp).
rewrite sepcon_emp; auto.
apply sepcon_derives; auto.
rewrite prop_true_andp.
apply now_later.
apply ptr_eq_refl; auto.
apply subp_i1.
simpl app.
rewrite links_cons_eq.
rewrite links_cons_eq.
autorewrite with norm. repeat rewrite prop_and; autorewrite with norm.
apply exp_left; intro z'.
apply exp_right with z'.
repeat rewrite sepcon_andp_prop'.
rewrite andp_comm. rewrite andp_assoc.
rewrite sepcon_comm.
repeat rewrite andp_assoc.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
subst v.
apply andp_right. apply prop_right; auto.
rewrite field_at_isptr.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
normalize.
apply andp_right.
repeat rewrite prop_and.
repeat apply andp_right; try solve [apply prop_right; auto].
rewrite <- andp_assoc.
apply andp_left1.
apply not_prop_right. intro. apply ptr_eq_e in H2. subst z.
apply ewand_conflict.
rewrite sepcon_comm.
repeat rewrite <- sepcon_assoc.
eapply derives_trans; [ apply sepcon_derives ; [ | apply derives_refl ]| ].
apply sepcon_derives ; [ | apply derives_refl ].
eapply derives_trans; [apply sepcon_derives | apply field_at__conflict]; 
  try apply field_at_field_at_; try apply list_struct_alignas_legal;
  try apply (list_link_size_in_range ls).
repeat rewrite FF_sepcon; auto.
normalize in H1.
apply andp_right.
Focus 2. apply andp_left2; apply andp_left1; auto.
rewrite sepcon_assoc.
rewrite <- andp_assoc.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply ewand_TT_sepcon.
rewrite andp_comm. rewrite unfash_sepcon_distrib.
apply sepcon_derives.
apply andp_left2. apply andp_left1; auto.
rewrite <- later_unfash.
eapply derives_trans.
eapply andp_derives. apply derives_refl. apply andp_derives.
apply sepcon_derives. apply derives_refl. apply now_later.
apply now_later.
rewrite <- later_sepcon.
repeat rewrite <- later_andp.
apply later_derives.
rewrite unfash_allp.
rewrite allp_andp1 by apply nil. apply allp_left with l.
rewrite unfash_allp.
rewrite allp_andp1 by apply Vundef. apply allp_left with z'.
eapply derives_trans.
apply andp_derives; [apply unfash_fash | apply derives_refl].
rewrite (sepcon_comm (field_at _ _ _ _ _)).
rewrite andp_comm.
eapply derives_trans; [ apply modus_ponens |  ].
apply andp_left1; auto.
Qed.
(*
Lemma links_unroll_right (ls: listspec list_struct list_link): forall sh l x z , 
    links ls sh l x z = 
             (!! (ptr_eq x z) && !! (l=nil) && emp) 
           || (!! (~ ptr_eq x z) && 
                EX h:val, EX r:list val, EX y:val, 
                    !!(l=r++h::nil /\ is_pointer_or_null z)  && 
             field_at sh list_struct list_link z y * 
             |> links ls sh r x y).
Proof.
Abort.  (* probably not true *)
*)

Fixpoint all_but_link (f: fieldlist) : fieldlist :=
 match f with
 | Fnil => Fnil
 | Fcons id t f' => if ident_eq id list_link
                               then f' 
                               else Fcons id t (all_but_link f')
 end.  

Definition elemtype (ls: listspec list_struct list_link) := reptype_structlist (all_but_link list_fields).

Definition add_link_back {ls: listspec list_struct list_link} {f: fieldlist}
  (v: reptype_structlist (all_but_link f)): reptype_structlist f.
  unfold all_but_link in v.
  induction f.
  + exact tt.
  + simpl in *; destruct (is_Fnil f) eqn:? ; destruct (ident_eq i list_link).
    - exact (default_val t).
    - destruct f; inversion Heqb. exact v.
    - exact (default_val t, v).
    - simpl in *.
      destruct (is_Fnil ((fix all_but_link (f : fieldlist) : fieldlist :=
               match f with
               | Fnil => Fnil
               | Fcons id t f' =>
                   if ident_eq id list_link
                   then f'
                   else Fcons id t (all_but_link f')
               end) f)).
       * exact (v, struct_default_val f).
       * destruct v as [v0 v1].
         exact (v0, IHf v1).
Defined.

Definition list_data {ls: listspec list_struct list_link} (v: elemtype ls): reptype list_struct.
  rewrite list_struct_eq.
  exact (add_link_back v).
Defined.

Definition list_cell (ls: listspec list_struct list_link) sh v p :=
  (field_at_ sh list_struct (StructField list_link :: nil) p) -* (data_at sh list_struct (list_data v) p).

Definition lseg' (ls: listspec list_struct list_link) (sh: share) := 
  HORec (fun (R: (list (elemtype ls))*(val*val) -> mpred) (lp: (list (elemtype ls))*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           !! is_pointer_or_null tail &&
                           list_cell ls sh h first
                           * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) first
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Definition lseg (ls: listspec list_struct list_link) (sh: share) (contents: list (elemtype ls)) (x y: val) : mpred :=
   lseg' ls sh (contents, (x,y)).

Lemma lseg_unfold (ls: listspec list_struct list_link): forall sh contents v1 v2,
    lseg ls sh contents v1 v2 = 
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                      !! is_pointer_or_null tail &&
                      list_cell ls sh h v1
                      * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) tail) v1
                      * |> lseg ls sh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros. unfold lseg.
 unfold lseg' at 1. rewrite HORec_fold_unfold.
  normalize.
 apply prove_HOcontractive; intros.
 destruct x. destruct l. 
 auto 50 with contractive.
 destruct p.
 auto 50 with contractive.
Qed.

Lemma lseg_eq (ls: listspec list_struct list_link):
  forall sh l v , 
  is_pointer_or_null v ->
    lseg ls sh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold ls sh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
destruct v; inv H; unfold Int.cmpu; rewrite Int.eq_true; auto.
apply pred_ext;
apply derives_extract_prop; intro.
contradiction H0.
destruct v; inv H; try split; auto; apply Int.eq_true.
inv H0.
Qed.

Definition lseg_cons (ls: listspec list_struct list_link) sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val, 
             !!(l=h::r  /\ is_pointer_or_null y) && 
             list_cell ls sh h x *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x * 
             |> lseg ls sh r y z.

Lemma lseg_unroll (ls: listspec list_struct list_link): forall sh l x z , 
    lseg ls sh l x z = 
      (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls sh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
apply derives_extract_prop; intros. 
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
apply orp_right1; auto.
apply orp_right2.
unfold lseg_cons.
apply derives_extract_prop; intros. 
apply exp_left; intro tail.
normalize.
apply exp_right with e. rewrite TT_andp.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'.
apply andp_right.
apply prop_right; split; auto.
auto.
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto. auto.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
inv H0. 
apply orp_left.
rewrite andp_assoc;
do 2 (apply derives_extract_prop; intro).
inv H0.
unfold lseg_cons.
apply derives_extract_prop; intros.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
symmetry in H0; inv H0.
 rewrite prop_true_andp by auto.
apply exp_right with y.
normalize.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_struct list_link):
   forall p P sh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_cell ls sh h v1 *
             (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) p) v1 *
               lseg ls sh tail p v2) ->
    P |-- lseg ls sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
 apply now_later.
Qed.

Lemma lseg_neq (ls: listspec list_struct list_link):
  forall sh s v v2,
    ptr_neq v v2 ->
     lseg ls sh s v v2 = lseg_cons ls sh s v v2.
intros. rewrite lseg_unroll.
apply pred_ext. apply orp_left; auto. 
rewrite andp_assoc.
do 2 (apply derives_extract_prop; intro). 
congruence.
apply orp_right2. auto.
Qed.

Lemma lseg_nonnull (ls: listspec list_struct list_link):
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg ls sh s v nullval = lseg_cons ls sh s v nullval.
Proof.
intros. unfold nullval.
apply lseg_neq.
destruct v; inv H; intuition; try congruence.
intro. apply ptr_eq_e in H. 
inv H.
inv H1.
intro. simpl in H. congruence.
Qed.

Lemma unfold_lseg_neq (ls: listspec list_struct list_link):
   forall P Q1 Q R v v2 sh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R))) |-- 
                        local (`ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R))) |--
     EX hry: elemtype ls * list (elemtype ls) * val,
      match hry with (h,r,y) => 
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h) v::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) v ::
                  |> `(lseg ls sh r) (`y) (v2) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg_cons ls sh s) v v2 :: R)))).
apply derives_trans with
(local (`ptr_neq v v2) && PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R)))).
apply andp_right; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl. 
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
 unfold_lift.
 unfold lseg_cons. simpl.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intros [? ?].
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 rewrite exp_sepcon1; apply exp_left; intro h.
 rewrite exp_sepcon1; apply exp_left; intro r.
 rewrite exp_sepcon1; apply exp_left; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 subst.
 apply exp_right with (h,r,y).
 repeat rewrite prop_true_andp by auto.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma unfold_lseg_cons (ls: listspec list_struct list_link):
   forall P Q1 Q R e sh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) e (`nullval) :: R))) |--
     EX hry: elemtype ls * list (elemtype ls) * val,
      match hry with (h,r,y) => 
       !! (s=h::r /\ is_pointer_or_null y) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h) e ::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) e ::
                  |> `(lseg ls sh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros. apply unfold_lseg_neq.
eapply derives_trans.
apply H. normalize.
unfold local. super_unfold_lift.
 intro rho.
apply derives_extract_prop0; intro.
unfold nullval.
normalize. destruct (e rho); inv H0; try congruence; auto.
intro. apply ptr_eq_e in H0. congruence.
Qed.

Lemma semax_lseg_neq (ls: listspec list_struct list_link):
  forall (Espec: OracleKind)
      Delta P Q sh s v v2 R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg ls sh s) v v2 :: R))) |-- 
                        local (`ptr_neq v v2)  ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val), 
    s=h::r -> is_pointer_or_null y ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h) v ::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y)) v ::
                  |> `(lseg ls sh r) (`y) v2 ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls sh s) v v2 :: R)))) 
       c Post.
Proof.
intros.
eapply semax_pre;  [apply unfold_lseg_neq; auto |].
normalize.
apply extract_exists_pre; intros [[h r] y].
apply semax_extract_prop; intros [? ?]; auto.
Qed.

Lemma semax_lseg_nonnull (ls: listspec list_struct list_link):
  forall (Espec: OracleKind)
      Delta P Q sh s v R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg ls sh s v nullval) :: R))) |-- 
                        !!(typed_true (tptr list_struct) v)  ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val), 
    s=h::r -> is_pointer_or_null y -> 
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh h v) ::
                  `(field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) v) ::
                  |> `(lseg ls sh r y nullval) ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls sh s v nullval) :: R)))) 
       c Post.
Proof.
intros.
apply semax_lseg_neq. eapply derives_trans.
apply H. unfold local. super_unfold_lift.
intro rho. normalize.
unfold nullval.
intro.
destruct v; inv H1; auto; congruence.
auto.
Qed.

Lemma lseg_nil_eq (ls: listspec list_struct list_link): 
    forall sh p q, lseg ls sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply andp_derives; auto.
rewrite prop_true_andp by auto. auto.
 unfold lseg_cons. normalize. inv H0.
 apply orp_right1.  rewrite andp_assoc.
 rewrite (prop_true_andp (_ = _)) by auto. auto.
Qed.

Lemma lseg_cons_eq (ls: listspec list_struct list_link):
     forall sh h r x z , 
    lseg ls sh (h::r) x z = 
        !!(~ ptr_eq x z) &&
         (EX  y : val,
          !!(is_pointer_or_null y) &&
   list_cell ls sh h x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x *
   |>lseg ls sh r y z).
Proof.
 intros. rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left.
 rewrite andp_assoc.
 apply derives_extract_prop; intro.
 apply derives_extract_prop; intro.
 inv H0.
 unfold lseg_cons.
 apply andp_derives; auto.
 apply exp_left; intro h0.
 apply exp_left; intro r0.
 apply exp_derives; intro y.
 repeat rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intros [? ?].
 symmetry in H; inv H.
 rewrite prop_true_andp by auto. auto.
 apply orp_right2.
 unfold lseg_cons.
 apply andp_derives; auto.
 apply exp_right with h. apply exp_right with r.
 apply exp_derives; intro y.
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
 apply andp_derives; auto.
 apply prop_derives; intuition.
Qed.

Definition lseg_cons_right (ls: listspec list_struct list_link) sh (l: list (elemtype ls)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(elemtype ls), EX r:list (elemtype ls), EX y:val, 
             !!(l=r++h::nil /\ is_pointer_or_null y)  && 
                       list_cell ls sh h y *
             field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             |> lseg ls sh r x y.

Lemma lseg_cons_right_neq (ls: listspec list_struct list_link): forall sh l x h y w z, 
             list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y * 
             lseg ls sh l x y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z
   |--   lseg ls sh (l++h::nil) x z * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z.
Proof.
intros.
rewrite (field_at_isptr _ _ _ _ z).
normalize.
assert (TT |-- ALL l: _, ALL x: val,
                   (((list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y) * lseg ls sh l x y)  
                          && (ewand (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z) TT))
                     >=> (lseg ls sh (l++h::nil) x z 
                                 && (ewand (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z) TT))).
Focus 2.
apply subp_e; eapply derives_trans;
   [apply H | apply allp_left with l; apply allp_left with x; auto].
forget (list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) y) as A.
forget (lseg ls sh (l ++ h :: nil) x z) as B.
forget (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) z) as C.
forget (lseg ls sh l x y) as D.
apply another_ewand_TT_lemma.
clear x l.
apply loeb.
apply allp_right; intro l.
apply allp_right; intro x.
destruct l.
rewrite lseg_nil_eq.
apply derives_trans with TT; auto.
apply subp_i1.
apply andp_left2.
rewrite sepcon_andp_prop.
rewrite andp_assoc.
apply derives_extract_prop; intro.
rewrite sepcon_emp.
simpl.
apply ptr_eq_e in H; subst y.
rewrite field_at_isptr.
normalize.
rewrite lseg_cons_eq.
apply andp_right; [ | apply andp_left2; auto].
apply andp_right.
apply not_prop_right; intro. apply ptr_eq_e in H; subst z.
apply ewand_conflict.
rewrite sepcon_assoc.
eapply derives_trans; [apply sepcon_derives; [apply derives_refl | ] | ].
apply field_at_conflict; [apply (list_link_size_in_range ls) |apply list_struct_alignas_legal].
normalize.
apply exp_right with z.
rewrite prop_true_andp by normalize.
rewrite lseg_nil_eq.
apply andp_left1.
rewrite prop_true_andp by (apply ptr_eq_refl; auto).
rewrite <- (sepcon_emp) at 1.
apply sepcon_derives; auto.
apply now_later.
apply subp_i1.
simpl app.
rewrite lseg_cons_eq.
rewrite lseg_cons_eq.
autorewrite with norm. repeat rewrite prop_and; autorewrite with norm.
apply exp_left; intro z'.
apply exp_right with z'.
repeat rewrite sepcon_andp_prop'.
rewrite andp_comm. rewrite andp_assoc.
rewrite sepcon_comm.
repeat rewrite andp_assoc.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
(* apply derives_extract_prop; intro. *)
rewrite field_at_isptr.
repeat rewrite sepcon_andp_prop'.
repeat rewrite sepcon_andp_prop.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
normalize.
apply andp_right.
repeat rewrite prop_and.
repeat apply andp_right; try solve [apply prop_right; auto].
rewrite <- andp_assoc.
apply andp_left1.
apply not_prop_right. intro. apply ptr_eq_e in H2. subst z.
apply ewand_conflict.
pull_left (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z') x).
pull_left (field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) w) x).
do 3 rewrite sepcon_assoc.
eapply derives_trans; [ apply sepcon_derives ; [ | apply derives_refl ]| ].
apply field_at_conflict; [apply (list_link_size_in_range ls) |apply list_struct_alignas_legal].
normalize.
rename H into H'; rename H1 into H; rename H0 into H1; rename H' into H0.
apply andp_right.
2: apply andp_left2; apply andp_left1; auto.
do 2 rewrite sepcon_assoc.
rewrite <- andp_assoc.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply ewand_TT_sepcon.
rewrite andp_comm. rewrite unfash_sepcon_distrib.
apply sepcon_derives.
apply andp_left2. apply andp_left1; auto.
rewrite <- later_unfash.
eapply derives_trans.
eapply andp_derives. apply derives_refl. apply andp_derives.
apply sepcon_derives. apply derives_refl. apply now_later.
apply now_later.
rewrite <- later_sepcon.
repeat rewrite <- later_andp.
apply later_derives.
rewrite unfash_allp.
rewrite allp_andp1 by apply nil. apply allp_left with l.
rewrite unfash_allp.
rewrite allp_andp1 by apply Vundef. apply allp_left with z'.
eapply derives_trans.
apply andp_derives; [apply unfash_fash | apply derives_refl].
rewrite (sepcon_comm (_ * field_at _ _ _ _ _)).
rewrite andp_comm.
eapply derives_trans; [ apply modus_ponens |  ].
apply andp_left1; auto.
Qed.

Lemma lseg_cons_right_null (ls: listspec list_struct list_link): forall sh l x h y, 
             list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * 
             lseg ls sh l x y
   |--   lseg ls sh (l++h::nil) x nullval.
Proof.
intros.
rewrite field_at_isptr; normalize.
assert (TT |-- ALL l: list (elemtype ls), ALL x: val,
                   (list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y * lseg ls sh l x y)  
                     >=> lseg ls sh (l++h::nil) x nullval).
Focus 2.
apply subp_e; eapply derives_trans; [apply H | apply allp_left with l; apply allp_left with x; auto].
clear x l.
apply loeb.
apply allp_right; intro l.
apply allp_right; intro x.
destruct l.
rewrite lseg_nil_eq.
apply derives_trans with TT; auto.
apply subp_i1.
apply andp_left2.
entailer.
  simpl app.
rewrite field_at_isptr.
entailer.
rewrite lseg_cons_eq.
apply andp_right.  apply prop_right. destruct y; inv Py; simpl; auto.
apply exp_right with nullval.
entailer!.
rewrite lseg_nil_eq.
rewrite prop_true_andp by (simpl; auto).
apply now_later.
apply subp_i1.
simpl app.
rewrite andp_comm.
rewrite lseg_cons_eq.
rewrite lseg_cons_eq.
autorewrite with norm.
apply exp_left; intro z.
apply exp_right with z.
repeat rewrite sepcon_andp_prop'.
rewrite andp_assoc.
rewrite sepcon_comm.
repeat rewrite andp_assoc.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
rewrite field_at_isptr.
normalize.
apply andp_right. apply prop_right; auto.
repeat split; auto.
intro. apply ptr_eq_e in H1. subst; inv Px.
forget (list_cell ls sh e x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) z) x) as A.
rewrite andp_comm.
repeat rewrite sepcon_assoc.
rewrite unfash_sepcon_distrib.
apply sepcon_derives.
apply andp_left2; auto.
rewrite <- later_unfash.
eapply derives_trans.
apply andp_derives; [apply derives_refl | ].
apply sepcon_derives; [apply derives_refl | apply now_later].
rewrite <- later_sepcon. rewrite <- later_andp.
apply later_derives.
rewrite unfash_allp.
rewrite allp_andp1 by apply nil. apply allp_left with l.
rewrite unfash_allp. rewrite allp_andp1 by apply Vundef. apply allp_left with z.
destruct l.
simpl.
rewrite lseg_nil_eq.
apply andp_left2.
normalize.
rewrite lseg_cons_eq.
rewrite field_at_isptr.
normalize.
apply exp_right with nullval.
apply andp_right.
apply prop_right.
fancy_intro. subst. subst. apply Py.
subst.
normalize.
rewrite lseg_nil_eq. normalize.
eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl | apply now_later]].
rewrite prop_true_andp by (simpl; auto).
rewrite sepcon_emp; auto.
eapply derives_trans.
apply andp_derives; [apply unfash_fash | apply derives_refl].
rewrite andp_comm. 
apply derives_trans
 with ((list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y *  lseg ls sh (e0::l) z y ) &&
   (list_cell ls sh h y * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) nullval) y *  lseg ls sh (e0::l) z y 
     --> lseg ls sh ((e0::l) ++ h :: nil) z nullval)).
2: apply modus_ponens.
apply andp_derives; auto.
rewrite sepcon_comm.
auto.
Qed.

(*
Lemma lseg_unroll_right (ls: listspec list_struct list_link): forall sh l x z , 
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)
*)
End LIST.

Hint Rewrite @lseg_nil_eq : norm.

Hint Rewrite @lseg_eq using reflexivity: norm.

Ltac simpl_list_cell := unfold list_cell; simpl_data_at.

Hint Rewrite @links_nil_eq @links_cons_eq : norm.

Lemma links_local_facts: 
  forall t fld LS sh contents p q, 
     @links t fld LS sh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite links_unfold.
destruct contents.
apply derives_extract_prop; intro.
unfold ptr_eq in H. 
apply prop_right.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0. subst.
apply int_eq_e in H. subst.
split; auto. split; auto.
destruct q; try contradiction.
destruct H; subst.
apply int_eq_e in H0. subst.
split; auto. split; auto.
normalize.
rewrite field_at_isptr.
normalize.
apply prop_right.
split; intro.
 subst q. contradiction H.
normalize.
inv H1.
Qed.
Hint Resolve links_local_facts : saturate_local.

Lemma lseg_local_facts: 
  forall t fld LS sh contents p q, 
     @lseg t fld LS sh contents p q |--
     !! (is_pointer_or_null p /\ (p=q <-> contents=nil)).
Proof.
intros.
rewrite lseg_unfold.
destruct contents.
apply derives_extract_prop; intro.
unfold ptr_eq in H. 
apply prop_right.
destruct p; try contradiction; simpl; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0.
apply int_eq_e in H. subst. subst.
split; auto; split; auto.
destruct q; try contradiction; auto.
destruct H.
apply int_eq_e in H0. subst.
split; auto; split; auto.
normalize.
rewrite field_at_isptr.
normalize.
apply prop_right.
split. intro; subst q.
contradiction H. normalize.
intros. inv H1.
Qed.
Hint Resolve lseg_local_facts : saturate_local.

(* Some lemmas about a particular specialization of linked lists,
  with one int and one link.
 This stuff generally works, but it's just too horrible with all the
 dependent types.  In contrast, when a particular list structure
  is instantiated with particular identifiers, then most of the
 dependent-type stuff simplifies away quite nicely.
 See the lemma linked_list_in_array in verif_reverse.v

Fixpoint list_init_rep (i: ident) (ofs: Z) (l: list int) :=
 match l with 
 | nil => nil
 | j::nil => Init_int32 j :: Init_int32 Int.zero :: nil
 | j::jl => Init_int32 j :: Init_addrof i (Int.repr (ofs+8)) :: list_init_rep i (ofs+8) jl
 end.

Definition intliststruct _struct _head _tail :=
 Tstruct _struct
     (Fcons _head tint (Fcons _tail (Tcomp_ptr _struct noattr) Fnil))
     noattr.

Lemma elemtype_intliststruct:
  forall ts _h _t (NEht: _h <> _t) (LS: listspec (intliststruct ts _h _t) _t),
            elemtype LS = int.
Proof.
intros.
unfold elemtype; destruct LS; simpl.
inversion list_struct_eq0.
subst. simpl.
rewrite if_false by auto.
rewrite if_true by auto.
reflexivity.
Qed.
 

Definition listelem2listint ts _h _t (NEht: _h <> _t) (LS: listspec (intliststruct ts _h _t) _t) (d: list (elemtype LS)) : list int 
  := (eq_rect (elemtype LS) (fun T : Type => list T) d int
     (elemtype_intliststruct ts _h _t NEht LS)).

Definition elem2int ts _h _t (NEht: _h <> _t) (LS: listspec (intliststruct ts _h _t) _t) (d: elemtype LS) : int 
  := (eq_rect (elemtype LS) (fun T : Type => T) d int (elemtype_intliststruct ts _h _t NEht LS)).

Lemma listelem2listint_cons: 
  forall ts _h _t (NEht: _h <> _t) (LS: listspec (intliststruct ts _h _t) _t) e el,
           listelem2listint _ _ _ NEht LS (e :: el) =
           (elem2int _ _ _ NEht LS e) :: (listelem2listint _ _ _ NEht LS el).
Proof.
intros. unfold listelem2listint, elem2int.
unfold eq_rect; simpl.
destruct (elemtype_intliststruct ts _h _t NEht LS).
reflexivity.
Qed.

Lemma listelem2listint_nil: 
  forall ts _h _t (NEht: _h <> _t) (LS: listspec (intliststruct ts _h _t) _t),
           listelem2listint _ _ _ NEht LS nil = nil.
Proof.
intros. unfold listelem2listint, elem2int.
unfold eq_rect; simpl.
destruct (elemtype_intliststruct ts _h _t NEht LS).
reflexivity.
Qed.

Lemma list_cell_eq: 
  forall ts _h _t (NEht: _h <> _t) (LS: listspec (intliststruct ts _h _t) _t),
  forall sh v i,
   list_cell LS sh v i = field_at sh (intliststruct ts _h _t) _h v 
         (Vint (elem2int _ _ _ NEht LS i)).
 intros. unfold list_cell.
 transitivity (structfieldsof sh (intliststruct ts _h _t) (Fcons _h tint Fnil) 0 0 v 
                           (elem2int _ _ _ NEht LS i)).
 admit.  (* how to prove this? *)
 simpl. rewrite withspacer_spacer. simpl. unfold spacer; simpl.
 apply emp_sepcon.
Qed.

Lemma linked_list_in_array:
 forall _struct _head _tail
       (NEht: _head <> _tail) 
       (LS: listspec (intliststruct _struct _head _tail) _tail)
  Delta i (data: list (elemtype LS)) n,
  (length data > 0)%nat ->
  (var_types Delta) ! i = None ->
  (glob_types Delta) ! i = Some (Global_var (tarray (intliststruct _struct _head _tail) n)) ->
   id2pred_star Delta Ews (tarray (intliststruct _struct _head _tail) n)
      (eval_var i (tarray (intliststruct _struct _head _tail) n)) 0 (list_init_rep i 0 (listelem2listint _ _ _ NEht LS data))
  |-- `(lseg LS Ews data) (eval_var i (tarray (intliststruct _struct _head _tail) n)) `nullval.
Proof. 
 pose proof I.
 intros.
 intro rho.
 unfold_lift.
 clear H.
 match goal with |- ?A |-- ?B =>
   assert (A |-- !! isptr (eval_var i (tarray (intliststruct _struct _head _tail) n) rho) && A)
 end.
 destruct data; [simpl in H0; omega | ].
 destruct data; repeat rewrite listelem2listint_cons; try rewrite listelem2listint_nil;
 simpl list_init_rep; unfold id2pred_star; fold id2pred_star;
 apply andp_right; auto;
 match goal with |- (_ * ?A) rho |-- _ => forget A as JJ end;
 simpl;  entailer!.
 eapply derives_trans; [apply H | clear H; apply derives_extract_prop; intro ].
 replace (eval_var i (tarray (intliststruct _struct _head _tail) n) rho)
   with (offset_val (Int.repr 0) (eval_var i (tarray (intliststruct _struct _head _tail) n) rho))
  by normalize.
 set (ofs:=0). clearbody ofs.
 revert ofs; induction data; intro.
* simpl in H0. omega.
*rewrite listelem2listint_cons.
 unfold list_init_rep; fold list_init_rep.
 destruct data.
+ clear IHdata.
 rewrite listelem2listint_nil.
 simpl.
 unfold_lift. 
 rewrite mapsto_isptr; rewrite sepcon_andp_prop'; apply derives_extract_prop; intro.
 destruct (eval_var i (tarray (intliststruct _struct _head _tail) n) rho); inv H. 
 apply @lseg_unroll_nonempty1 with nullval; simpl; auto.
 rewrite mapsto_tuint_tint.
 rewrite (list_cell_eq _ _ _ NEht LS).
 match goal with |- context [mapsto ?sh tint ?v1 ?v2 * emp] =>
   replace (mapsto sh tint v1 v2) with 
       (mapsto sh (tptr (intliststruct _struct _head _tail)) v1 nullval)
  by (symmetry; apply mapsto_null_mapsto_pointer)
 end.
apply sepcon_derives;
 [eapply mapsto_field_at'; try reflexivity; try apply I;
   unfold offset_val; repeat rewrite Int.add_assoc
 | ].
 simpl. rewrite if_true by auto. reflexivity.
 unfold field_offset; simpl. rewrite if_true by auto. reflexivity.
apply sepcon_derives;
 [eapply mapsto_field_at'; try reflexivity; try apply I;
   unfold offset_val; repeat rewrite Int.add_assoc
 | ].
 simpl. rewrite if_false by auto; do 2 rewrite if_true by auto. reflexivity.
 unfold field_offset. simpl. rewrite if_false by auto; rewrite if_true by auto. reflexivity.
 f_equal. f_equal. unfold Int.zero. repeat rewrite add_repr.
 simpl. change (align (align 4 4) 4) with (4+0). rewrite Z.add_assoc.
reflexivity.
 rewrite @lseg_nil_eq; auto.
 entailer. compute; auto.
 +
  spec IHdata. simpl length in H0|-*. repeat rewrite inj_S in H0|-*. omega.
 specialize (IHdata (ofs+8)).
 forget (list_init_rep i (ofs+8)(listelem2listint _struct _head _tail NEht LS (e::data))) as rep'.
 rewrite listelem2listint_cons.
 unfold id2pred_star. fold id2pred_star.
 simpl init_data2pred'.
 repeat (rewrite H1; rewrite H2). unfold tarray at 2.
  apply @lseg_unroll_nonempty1 with (offset_val (Int.repr (ofs + 8))
       (eval_var i (tarray (intliststruct _struct _head _tail) n) rho)).
  destruct (eval_var i (tarray (intliststruct _struct _head _tail) n) rho); inv H; clear; compute; auto.
  destruct (eval_var i (tarray (intliststruct _struct _head _tail) n) rho); inv H; clear; compute; auto.
  rewrite (list_cell_eq _ _ _ NEht LS).
  rewrite mapsto_tuint_tint.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives.
 unfold_lift. simpl.
apply sepcon_derives; eapply mapsto_field_at'; try reflexivity.
 simpl. rewrite if_true by auto. reflexivity.
 unfold field_offset. simpl. rewrite if_true by auto. reflexivity.
 simpl. rewrite if_false by auto; do 2 rewrite if_true by auto. reflexivity.
 unfold field_offset. simpl. rewrite if_false by auto; rewrite if_true by auto. reflexivity.
 normalize. destruct (eval_var i (tarray (intliststruct _struct _head _tail) n) rho); inv H; hnf; auto.
 replace (ofs + init_data_size (Init_int32 _) +
   init_data_size (Init_addrof i (Int.repr (ofs + 8))))
   with (ofs+8).
 apply IHdata. simpl; omega.
Qed.
*)

Lemma field_at_ptr_neq: forall sh t fld p1 p2 v1 v2,
 0 < sizeof (nested_field_type2 t (fld :: nil)) < Int.modulus ->
 legal_alignas_type t = true ->
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2
   |--
   !! (~ ptr_eq p1 p2).
Proof.
   intros.
   apply not_prop_right; intros.
   apply ptr_eq_e in H1; rewrite -> H1.
   apply field_at_conflict; assumption.
Qed.

Lemma field_at_ptr_neq_andp_emp: forall sh t fld p1 p2 v1 v2,
 0 < sizeof (nested_field_type2 t (fld :: nil)) < Int.modulus ->
 legal_alignas_type t = true ->
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2
   |--
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2 *
   (!! (~ ptr_eq p1 p2) && emp).
Proof.
   intros.
   normalize.
   apply andp_right.
   apply field_at_ptr_neq; assumption.
   cancel.
Qed.

Lemma field_at_ptr_neq_null: forall sh t fld v p,  
   field_at sh t fld v p |-- !! (~ ptr_eq p nullval).
Proof.
   intros.
   rewrite -> field_at_isptr.
   entailer!.
   destruct p; unfold nullval; simpl in *; tauto.
Qed.

(* About Power later *************************)

Fixpoint power_later (n:nat) P := 
    match n with
    | 0%nat => P
    | S n' => later (power_later n' P)
    end
.

Lemma power_now_later: forall n P, P |-- power_later n P.
Proof.
   induction n.
   (* Base step *)
   intros. unfold power_later.
   apply derives_refl.
   (* Induction step *)
   intros. simpl.
   apply derives_trans with (power_later n P).
   apply IHn. apply now_later.
Qed.

Lemma power_later_andp: forall (n:nat) (P Q : mpred), power_later n (P && Q) = (power_later n P) && (power_later n Q).
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. apply later_andp.
Qed.

Lemma power_later_exp': forall (n:nat) T (any:T) F, 
     power_later n (EX x:T, F x) = EX x:T, (power_later n (F x)).
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> (IHn T any). apply (later_exp' T any).
Qed.

Lemma power_later_sepcon: forall n P Q, power_later n (P * Q) = (power_later n P) * (power_later n Q).
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. apply later_sepcon.
Qed.

Lemma power_later_connect: forall n P, power_later n (|> P) = power_later (n + 1) P.
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. reflexivity.
Qed.

Lemma power_later_connect': forall n P, |> (power_later n P) = power_later (n + 1) P.
Proof.
   induction n; intros; simpl.
   reflexivity.
   rewrite -> IHn. reflexivity.
Qed.

Lemma power_later_derives: forall n:nat, forall P Q:mpred,
   P |-- Q -> (power_later n P) |-- (power_later n Q).
Proof.
   induction n; intros; simpl.
   assumption.
   apply later_derives. apply IHn. assumption.
Qed.

Lemma power_later_TT: forall n, TT = power_later n TT.
Proof.
   intros.
   apply pred_ext.
   apply power_now_later.
   normalize.
Qed.

Lemma corable_power_later: forall n P, corable P -> corable (power_later n P).
Proof.
  intros.
  induction n; simpl.
  + exact H.
  + exact (corable_later _ IHn).
Qed.

Ltac power_normalize :=
    repeat (
      try rewrite -> power_later_andp;
      try rewrite -> power_later_sepcon;
      try rewrite <- power_later_TT)
.

Lemma power_later_erase: forall n P Q R, P * Q |-- R -> power_later n P * Q |-- power_later n R.
Proof.
  intros.
  apply derives_trans with (power_later n (P * Q)).
  power_normalize.
  cancel.
  apply power_now_later.
  apply power_later_derives.
  assumption.
Qed.

Lemma power_prop_andp_sepcon: 
  forall (n:nat) P Q R, ((power_later n (!! P)) && Q) * R = (power_later n (!! P)) && (Q * R).
Proof.
  intros.
  apply (corable_andp_sepcon1 (power_later n (!! P))).
  apply corable_power_later.
  exact (corable_prop P).
Qed.

Definition lseg_cell {list_struct : type} {list_link : ident} (ls : listspec list_struct list_link) (sh : share) (v: elemtype ls) (x y: val) := !!is_pointer_or_null y && list_cell ls sh v x * field_at sh list_struct (StructField list_link :: nil) (valinject (nested_field_type2 list_struct (StructField list_link :: nil)) y) x.

Lemma lseg_cons_eq2: forall {list_struct : type} {list_link : ident}
  (ls : listspec list_struct list_link) (sh : share) (h : elemtype ls) (r : list (elemtype ls)) 
  (x z : val), lseg ls sh (h :: r) x z =
  !!(~ ptr_eq x z) && (EX  y : val, lseg_cell ls sh h x y * |>lseg ls sh r y z).
Proof.
  intros.
  rewrite -> lseg_cons_eq.
  unfold lseg_cell.
  reflexivity.
Qed.

Lemma power_list_append: forall {sh: share} {list_struct : type} {list_link : ident}
  {ls : listspec list_struct list_link} (n:nat) (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls sh x tl tl' * P tl |-- FF) ->
  power_later n (lseg ls sh ct1 hd mid) * lseg ls sh ct2 mid tl * P tl|--
  power_later n (lseg ls sh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  revert hd n.
  induction ct1; intros.
  + simpl.
    rewrite -> lseg_nil_eq. cancel.
    apply power_later_erase.
    normalize.
  + simpl.
    repeat rewrite -> lseg_cons_eq2.
    power_normalize.      
    repeat (try rewrite -> (power_later_exp' n val hd)).
    normalize.
    apply exp_right with x.
    repeat rewrite power_prop_andp_sepcon.
    apply andp_right; apply andp_left2.
    - (* Prop part *)
      rewrite sepcon_assoc.
      apply power_later_erase.
      apply not_prop_right; intros.
      apply ptr_eq_e in H0; rewrite H0.
      apply derives_trans with (lseg_cell ls sh a tl x * P tl * TT); [cancel|].
      apply (derives_left_sepcon_right_corable FF (lseg_cell ls sh a tl x * P tl)); [apply corable_prop | apply H].
    - power_normalize.
      repeat rewrite sepcon_assoc.
      apply sepcon_derives; [cancel|].
      repeat rewrite power_later_connect.
      normalize.
      (* normalize is over powerful here. Originally, I am supposed to use IH afterwards*)
Qed.

Lemma list_append: forall {sh: share} {list_struct : type} {list_link : ident}
  {ls : listspec list_struct list_link} (hd mid tl:val) ct1 ct2 P,
  (forall x tl', lseg_cell ls sh x tl tl' * P tl |-- FF) ->
  (lseg ls sh ct1 hd mid) * lseg ls sh ct2 mid tl * P tl|--
  (lseg ls sh (ct1 ++ ct2) hd tl) * P tl.
Proof.
  intros.
  pose proof power_list_append 0 hd mid tl ct1 ct2 P H.
  simpl in H0.
  exact H0.
Qed.


