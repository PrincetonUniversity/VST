Require Import floyd.proofauto.

Local Open Scope logic.

Class listspec (list_struct: type) (list_link: ident) :=
  mk_listspec {  
   list_fields: fieldlist;
   list_structid: ident;
   list_struct_eq: list_struct= Tstruct list_structid list_fields noattr;
   list_link_type: (type_of_field
          (unroll_composite_fields list_structid list_struct list_fields)
          list_link) = tptr list_struct
}.

Section LIST.
Context  {list_struct: type} {list_link: ident}.

Definition links' (ls: listspec list_struct list_link) (sh: share) := 
  HORec (fun (R: (list val)*(val*val) -> mpred) (lp: (list val)*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (h=first /\ ~ (ptr_eq first last)) && 
                        EX tail:val, 
                           field_mapsto sh list_struct list_link first tail
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
                           field_mapsto sh list_struct list_link v1 tail
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
             field_mapsto sh list_struct list_link x y * 
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
rewrite (field_mapsto_typecheck_val list_struct list_link sh v tail list_structid list_fields noattr)
  by apply list_struct_eq.
try rewrite typecheck_val_eq.
rewrite list_link_type.
rewrite sepcon_andp_prop';
apply derives_extract_prop; intro;
 apply prop_right; auto.
auto.
apply exp_left; intro r'.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H3.
apply andp_right.
apply prop_right; auto.
apply exp_right with y.
 auto.
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
rewrite prop_true_andp by auto.
apply exp_right with l.
apply exp_right with tail.
normalize.
apply andp_right.
erewrite (field_mapsto_typecheck_val list_struct list_link sh v tail).
try rewrite typecheck_val_eq.
rewrite list_link_type.
simpl.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intro.
apply prop_right; auto.
apply list_struct_eq.
auto.
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
auto.
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
   field_mapsto sh list_struct list_link x y *
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
destruct x; simpl; auto. destruct z; simpl; auto. destruct (Int.eq i i0); auto.
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
             field_mapsto sh list_struct list_link y nullval * 
             links ls sh l x y
   |--   links ls sh (l++y::nil) x nullval.
Proof.
intros.
assert (TT |-- ALL l: list val, ALL x: val,
                   (field_mapsto sh list_struct list_link y nullval * links ls sh l x y)  
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
rewrite field_mapsto_isptr.
apply derives_extract_prop; intro.
rewrite links_cons_eq.
apply andp_right.  apply prop_right; auto.
split; auto. intro. apply ptr_eq_e in H0. subst. apply H.
apply exp_right with nullval.
rewrite prop_true_andp by (simpl; auto).
rewrite links_nil_eq.
rewrite prop_true_andp by reflexivity.
apply derives_trans with (field_mapsto sh list_struct list_link x nullval * emp).
rewrite sepcon_emp; auto.
apply sepcon_derives; auto.
apply now_later.
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
rewrite field_mapsto_isptr.
normalize.
apply andp_right. apply prop_right; auto.
intro. apply ptr_eq_e in H2. subst; apply H.
apply andp_right. apply prop_right; auto.
normalize in H1.
rewrite prop_true_andp by auto.
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
apply ptr_eq_e in H2. subst z.
rewrite links_cons_eq.
rewrite field_mapsto_isptr.
apply derives_extract_prop; intro.
rewrite prop_true_andp.
2: split; auto; intro Hx; destruct y; inv H2; inv Hx.
apply exp_right with nullval.
rewrite prop_true_andp by (simpl; auto).
rewrite links_nil_eq.
rewrite prop_true_andp by reflexivity.
eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl | apply now_later]].
rewrite sepcon_emp; auto.
eapply derives_trans.
apply andp_derives; [apply unfash_fash | apply derives_refl].
rewrite andp_comm. 
apply derives_trans
 with ((field_mapsto sh list_struct list_link y nullval *  links ls sh (v::l) z y ) &&
   (field_mapsto sh list_struct list_link y nullval *  links ls sh (v::l) z y 
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

Lemma links_cons_right_null' (ls: listspec list_struct list_link): forall sh l x y, 
     links ls sh (l++y::nil) x nullval
    |-- links ls sh l x y * |> field_mapsto sh list_struct list_link y nullval.
Proof.
(* Not provable.  The subtle reason is:
  If l<>nil, cannot prove that x<>y.
  One can prove that later-later-later, x<>y, but not now x<>y.
*)
Abort.


Lemma another_ewand_TT_lemma:
 forall A B C: mpred, A && ewand C TT >=> B && ewand C TT |-- A*C >=> B*C.
Admitted.


Lemma links_cons_right (ls: listspec list_struct list_link): forall sh l x y z w, 
             field_mapsto sh list_struct list_link y z * 
             field_mapsto sh list_struct list_link z w * 
             links ls sh l x y
   |--   links ls sh (l++y::nil) x z * field_mapsto sh list_struct list_link z w.
Proof.
intros.
assert (TT |-- ALL l: list val, ALL x: val,
                   ((field_mapsto sh list_struct list_link y z * links ls sh l x y)  
                          && (ewand (field_mapsto sh list_struct list_link z w) TT))
                     >=> (links ls sh (l++y::nil) x z && (ewand (field_mapsto sh list_struct list_link z w) TT))).
Focus 2.
apply subp_e; eapply derives_trans; [apply H | apply allp_left with l; apply allp_left with x; auto].
forget (field_mapsto sh list_struct list_link y z) as A.
forget (links ls sh (l ++ y :: nil) x z) as B.
forget (field_mapsto sh list_struct list_link z w) as C.
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
rewrite field_mapsto_isptr.
rewrite andp_assoc.
apply derives_extract_prop; intro.
rewrite links_cons_eq.
apply andp_right; [ | apply andp_left2; auto].
apply andp_right.
rewrite prop_and; rewrite prop_true_andp by auto.
apply not_prop_right; intro. apply ptr_eq_e in H0; subst z.
apply ewand_conflict.
eapply derives_trans; [apply sepcon_derives | apply field_mapsto__conflict]; 
  apply field_mapsto_field_mapsto_.
apply exp_right with z.
normalize.
rewrite links_nil_eq.
erewrite field_mapsto_typecheck_val at 1.
2: apply list_struct_eq.
rewrite list_link_type.
normalize.
simpl in H0.
apply andp_left1.
apply derives_trans with (field_mapsto sh list_struct list_link x z * emp).
rewrite sepcon_emp; auto.
apply sepcon_derives; auto.
apply now_later.
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
rewrite field_mapsto_isptr.
repeat rewrite sepcon_andp_prop'.
repeat rewrite andp_assoc.
apply derives_extract_prop; intro.
normalize.
apply andp_right.
rewrite <- andp_assoc.
apply andp_left1.
apply not_prop_right. intro. apply ptr_eq_e in H2. subst z.
apply ewand_conflict.
rewrite sepcon_comm.
repeat rewrite <- sepcon_assoc.
eapply derives_trans; [ apply sepcon_derives ; [ | apply derives_refl ]| ].
apply sepcon_derives ; [ | apply derives_refl ].
eapply derives_trans; [apply sepcon_derives | apply field_mapsto__conflict]; 
  apply field_mapsto_field_mapsto_.
repeat rewrite FF_sepcon; auto.
normalize in H1.
rewrite prop_true_andp by auto.
rewrite prop_true_andp by auto.
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
rewrite (sepcon_comm (field_mapsto _ _ _ _ _)).
rewrite andp_comm.
eapply derives_trans; [ apply modus_ponens |  ].
apply andp_left1; auto.
Qed.

Lemma links_unroll_right (ls: listspec list_struct list_link): forall sh l x z , 
    links ls sh l x z = 
             (!! (ptr_eq x z) && !! (l=nil) && emp) 
           || (!! (~ ptr_eq x z) && 
                EX h:val, EX r:list val, EX y:val, 
                    !!(l=r++h::nil)  && 
             field_mapsto sh list_struct list_link y z * 
             |> links ls sh r x y).
Proof.
Abort.  (* probably not true *)

Fixpoint all_but_link (ls: listspec list_struct list_link) (f: fieldlist) : fieldlist :=
 match f with
 | Fnil => Fnil
 | Fcons id t f' => if ident_eq id list_link
                               then f' 
                               else Fcons id t (all_but_link ls f')
 end.  

Definition elemtype (ls: listspec list_struct list_link) := reptype_structlist (all_but_link ls list_fields).

Definition list_cell (ls: listspec list_struct list_link) sh p v :=
   structfieldsof sh list_struct (all_but_link ls list_fields) 0 0 p v.

Definition lseg' (ls: listspec list_struct list_link) (sh: share) := 
  HORec (fun (R: (list (elemtype ls))*(val*val) -> mpred) (lp: (list (elemtype ls))*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           list_cell ls sh first h
                           * field_mapsto sh list_struct list_link first tail
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
                      list_cell ls sh v1 h
                      * field_mapsto sh list_struct list_link v1 tail
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
             list_cell ls sh x h *
             field_mapsto sh list_struct list_link x y * 
             |> lseg ls sh r y z.

(*
Lemma lseg_neq (ls: listspec list_struct list_link):  forall sh l x z , 
  typecheck_val x (tptr list_struct) = true ->
  typecheck_val z (tptr list_struct) = true ->
  ptr_neq x z -> 
    lseg ls sh l x z = lseg_cons ls sh l x z.
Proof.
unfold lseg_cons, ptr_neq; intros.
rewrite lseg_unfold at 1; auto.
destruct l.
apply pred_ext; apply derives_extract_prop; intro.
contradiction. clear H2.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H2.
apply pred_ext; apply derives_extract_prop; intro.
clear H2.
apply exp_left; intro tail.
apply andp_right; try apply prop_right; auto.
apply exp_right with e.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'; apply andp_right.
rewrite (field_mapsto_typecheck_val list_struct list_link sh x tail list_structid list_fields noattr)
  by apply list_struct_eq.
rewrite list_link_type.
rewrite sepcon_andp_prop.
rewrite sepcon_andp_prop'.
apply derives_extract_prop; intro.
apply prop_right; auto.
auto.
apply exp_left; intro h.
apply exp_left; intro r'.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H3.
apply andp_right.
apply prop_right; auto.
apply exp_right with y.
 auto.
Qed.*)

Lemma lseg_unroll (ls: listspec list_struct list_link): forall sh l x z , 
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons ls sh l x z.
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
rewrite prop_true_andp by auto.
apply exp_right with e.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'.
apply andp_right.
erewrite (field_mapsto_typecheck_val list_struct list_link sh x tail); try reflexivity.
try rewrite typecheck_val_eq.
rewrite list_link_type.
rewrite sepcon_andp_prop.
rewrite sepcon_andp_prop'.
apply derives_extract_prop; intro. 
apply prop_right; split; auto.
apply list_struct_eq.
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
auto.
Qed.

Lemma lseg_unroll_nonempty1 (ls: listspec list_struct list_link):
   forall p P sh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    is_pointer_or_null p ->
    P |-- list_cell ls sh v1 h *
             (field_mapsto sh list_struct list_link v1 p *
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


Lemma lift2_lseg_cons (ls: listspec list_struct list_link): 
 forall sh s p q, `(lseg_cons ls sh s)  p q =
    EX hry:(elemtype ls * list (elemtype ls) * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (`ptr_neq p q) &&
       (`(list_cell ls sh) p (`h) *
        `(field_mapsto sh list_struct list_link) p (`y) *
        |> `(lseg ls sh r) (`y) q))
     end.
Proof.
 intros.
 unfold lseg_cons, ptr_neq; unfold_lift. extensionality rho. simpl.
 apply pred_ext.
 apply derives_extract_prop; intro.
 apply exp_left; intro h.
 apply exp_left; intro r.
 apply exp_left; intro y.
do 2 rewrite sepcon_andp_prop'.
apply derives_extract_prop; intros [? ?].
inv H0. 
 apply exp_right with (h, r, y).
 rewrite prop_true_andp by auto.
 normalize.
 apply exp_left; intros [[h r] y].
 apply derives_extract_prop; intro.
 inv H.
 unfold local, lift1.
 apply derives_extract_prop; intro.
 rewrite prop_true_andp by auto.
 apply exp_right with h.
 apply exp_right with r.
 apply exp_right with y.
 do 2 rewrite sepcon_andp_prop'.
 apply andp_right.
 erewrite (field_mapsto_typecheck_val); [ | apply list_struct_eq].
 try rewrite typecheck_val_eq.
 rewrite list_link_type.
 rewrite sepcon_andp_prop.
 rewrite sepcon_andp_prop'.
 apply derives_extract_prop; intro.
 apply prop_right; auto.
 auto.
Qed.



Lemma unfold_lseg_neq (ls: listspec list_struct list_link):
   forall P Q1 Q R v v2 sh s,
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R))) |-- 
                        local (`ptr_neq v v2) ->
      PROPx P (LOCALx (Q1::Q) (SEPx (`(lseg ls sh s) v v2 :: R))) |--
     EX hry: elemtype ls * list (elemtype ls) * val,
      match hry with (h,r,y) => 
       !! (s=h::r) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh) v (`h) ::
                  `(field_mapsto sh list_struct list_link) v (`y) ::
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
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue; unfold_lift; simpl.
unfold lift1; simpl. 
 repeat (apply derives_extract_prop; intro).
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by auto.
apply sepcon_derives; auto.
rewrite lseg_neq; auto.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
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
       !! (s=h::r) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
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
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val), s=h::r ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh) v (`h) ::
                  `(field_mapsto sh list_struct list_link) v (`y) ::
                  |> `(lseg ls sh r) (`y) v2 ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls sh s) v v2 :: R)))) 
       c Post.
Proof.
intros.
eapply semax_pre;  [apply unfold_lseg_neq | ].
eapply derives_trans; [ | apply H].
normalize.
apply extract_exists_pre; intros [[h r] y].
apply semax_extract_prop; intro; auto.
Qed.

Lemma semax_lseg_nonnull (ls: listspec list_struct list_link):
  forall (Espec: OracleKind)
      Delta P Q sh s e R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg ls sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e)  ->
  (forall (h: elemtype ls) (r: list (elemtype ls)) (y: val), s=h::r ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell ls sh) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg ls sh r) (`y) `nullval ::
                  R)))) c Post) ->
   semax Delta 
       (PROPx P (LOCALx Q (SEPx (`(lseg ls sh s) e `nullval :: R)))) 
       c Post.
Proof.
intros.
apply semax_lseg_neq. eapply derives_trans.
apply H. unfold local. super_unfold_lift.
intro rho. normalize.
unfold nullval.
intro.
destruct (e rho); inv H1; auto; congruence.
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
   list_cell ls sh x h * field_mapsto sh list_struct list_link x y *
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
             !!(l=r++h::nil)  && 
                       list_cell ls sh y h *
             field_mapsto sh list_struct list_link y z * 
             |> lseg ls sh r x y.

Lemma lseg_cons_right_null (ls: listspec list_struct list_link): forall sh l x h y, 
             list_cell ls sh y h * field_mapsto sh list_struct list_link y nullval * 
             lseg ls sh l x y
   |--   lseg ls sh (l++h::nil) x nullval.
Proof.
intros.
assert (TT |-- ALL l: list (elemtype ls), ALL x: val,
                   (list_cell ls sh y h * field_mapsto sh list_struct list_link y nullval * lseg ls sh l x y)  
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
repeat rewrite sepcon_andp_prop.
 apply derives_extract_prop; intro.
 rewrite sepcon_emp. simpl app.
 apply ptr_eq_e in H; subst y.
rewrite field_mapsto_isptr.
repeat rewrite sepcon_andp_prop.
 apply derives_extract_prop; intro.
rewrite lseg_cons_eq.
apply andp_right.  apply prop_right; auto.
intro. apply ptr_eq_e in H0. subst. apply H.
apply exp_right with nullval.
 rewrite prop_true_andp by reflexivity.
rewrite lseg_nil_eq.
 rewrite prop_true_andp by reflexivity.
cancel. apply now_later.
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
rewrite field_mapsto_isptr.
normalize.
apply andp_right. apply prop_right; auto.
intro. apply ptr_eq_e in H2. subst; apply H1.
normalize in H0.
apply andp_right. apply prop_right; auto.
apply andp_right. apply prop_right; auto.
forget (list_cell ls sh x e * field_mapsto sh list_struct list_link x z) as A.
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
rewrite lseg_nil_eq.
apply andp_left2.
normalize. apply ptr_eq_e in H2. subst z.
rewrite lseg_cons_eq.
rewrite field_mapsto_isptr.
normalize.
apply exp_right with nullval.
apply andp_right.
apply prop_right.
intro. apply ptr_eq_e in H3. subst. apply H2.
normalize.
rewrite lseg_nil_eq. normalize.
eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl | apply now_later]].
rewrite sepcon_emp; auto.
eapply derives_trans.
apply andp_derives; [apply unfash_fash | apply derives_refl].
rewrite andp_comm. 
apply derives_trans
 with ((list_cell ls sh y h * field_mapsto sh list_struct list_link y nullval *  lseg ls sh (e0::l) z y ) &&
   (list_cell ls sh y h * field_mapsto sh list_struct list_link y nullval *  lseg ls sh (e0::l) z y 
     --> lseg ls sh ((e0::l) ++ h :: nil) z nullval)).
2: apply modus_ponens.
apply andp_derives; auto.
rewrite sepcon_comm.
auto.
Qed.


Lemma lseg_unroll_right (ls: listspec list_struct list_link): forall sh l x z , 
    lseg ls sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right ls sh l x z.
Abort.  (* not likely true *)

End LIST.

Hint Rewrite @lseg_nil_eq : norm.

Hint Rewrite @lseg_eq using reflexivity: norm.

Ltac simpl_list_cell := unfold list_cell; simpl_typed_mapsto.
