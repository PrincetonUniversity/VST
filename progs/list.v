Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Fixpoint fields_mapto (sh: Share.t) (t1: type) (flds: list ident) (v1: val) (v2: list val) : mpred :=
  match flds, v2 with
  | nil, nil => emp
  | i::flds', vt::v2' => field_mapsto sh t1 i v1 vt * fields_mapto sh t1 flds' v1 v2'
  | _, _ => FF
  end.

Fixpoint field_names (flds: fieldlist) : list ident :=
  match flds with
  | Fnil => nil
  | Fcons i t flds' => i :: field_names flds'
  end.

Definition struct_fields_mapto (sh: Share.t) (t1: type) (v1: val) (v2: list (val)) : mpred :=
  match t1 with
  | Tstruct id fList  att =>
         fields_mapto sh t1 (field_names fList) v1 v2
  | _  => FF
  end.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 => Int.cmpu Ceq n1 n2 = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Int.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Definition ptr_neq (v1 v2: val) := ~ ptr_eq v1 v2.

Fixpoint fieldnames (f: fieldlist) : list ident :=
 match f with
 | Fcons id _ f' => id :: fieldnames f'
 | Fnil => nil
 end.

Fixpoint other_fields (id: ident) (f: fieldlist) : list (ident * type) :=
 match f with
 | Fcons i t f' => if eq_dec i id then other_fields id f' else (i,t)::other_fields id f'
 | Fnil => nil
 end.

Record multilistspec := mk_multilistspec {
 mlist_structid: ident;
 mlist_link: ident;
 mlist_fields: fieldlist;
 mlist_fields_norepet: list_norepet (fieldnames mlist_fields);
 mlist_other_props:
    forall x, In x (other_fields mlist_link mlist_fields) ->
              (forall T, unroll_composite mlist_structid T (snd x) = snd x) /\
              exists ch, access_mode (snd x) = By_value ch
}.

Definition mlist_struct (ls: multilistspec) : type :=
 Tstruct (mlist_structid ls) (mlist_fields ls) noattr.

Definition mlist_type (ls: multilistspec) := Tpointer (mlist_struct ls) noattr.
Definition mlist_data_fieldnames (ls: multilistspec) : list ident :=
     map (@fst _ _) (other_fields (mlist_structid ls) (mlist_fields ls)).

Class listspec (list_structid: ident) (list_data: ident) (list_dtype: type) (list_link: ident) :=
  mk_listspec {  
   list_struct: type := (Tstruct list_structid 
       (Fcons list_data list_dtype
        (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)) noattr);
   list_data_not_link: list_data<>list_link;
   list_unroll_dtype:
              forall T, unroll_composite list_structid T list_dtype = list_dtype;
   list_access_mode: exists ch, access_mode list_dtype = By_value ch
}.

Section LIST.
Context  {list_structid} {list_data} {list_dtype} {list_link} (ls: listspec list_structid list_data list_dtype list_link).

Definition lseg' (sh: share) := 
  HORec (fun (R: (list val)*(val*val) -> mpred) (lp: (list val)*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           field_mapsto sh list_struct list_data first h 
                           * field_mapsto sh list_struct list_link first tail
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Definition lseg  (sh: share) (contents: list val) (x y: val) : mpred :=
   lseg' sh (contents, (x,y)).

Lemma lseg_unfold: forall sh contents v1 v2,
    lseg sh contents v1 v2 = 
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                       field_mapsto sh list_struct list_data v1 h 
                      * field_mapsto sh list_struct list_link v1 tail
                      * |> lseg sh t tail v2
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

Lemma lseg_eq:
  forall sh l v , 
  typecheck_val v (tptr list_struct) = true ->
    lseg sh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold sh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
unfold typecheck_val in H.
destruct v; simpl in H; try discriminate.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
split; auto. 
unfold Int.cmpu.
rewrite Int.eq_true. auto.
normalize.
replace (v0 :: l = nil) with False by (apply prop_ext; intuition; congruence).
apply pred_ext; normalize.
contradiction H0.
unfold ptr_eq, typecheck_val in H|-*.
destruct v; inv H; auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
Qed.

Definition lseg_cons sh (l: list val) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:val, EX r:list val, EX y:val, 
             !!(l=h::r 
                /\ typecheck_val h list_dtype  = true/\ typecheck_val y (tptr list_struct) = true) && 
             field_mapsto sh list_struct list_data x h * 
             field_mapsto sh list_struct list_link x y * 
             |> lseg sh r y z.


Lemma lseg_neq:  forall sh l x z , 
  typecheck_val x (tptr list_struct) = true ->
  typecheck_val z (tptr list_struct) = true ->
  ptr_neq x z -> 
    lseg sh l x z = lseg_cons sh l x z.
Proof.
unfold lseg_cons, ptr_neq; intros.
rewrite lseg_unfold at 1; auto.
destruct l.
apply pred_ext; normalize.
intros.
inv H2.
apply pred_ext; normalize.
apply exp_right with v; normalize.
apply exp_right with l; normalize.
apply exp_right with tail; normalize.
apply andp_right; auto.
rewrite (field_mapsto_typecheck_val list_struct list_data sh x v 
                        list_structid 
                    (Fcons list_data list_dtype
                        (Fcons list_link (Tcomp_ptr list_structid noattr)
                           Fnil))  noattr); auto.
assert (UNROLL: unroll_composite_fields list_structid list_struct
       (Fcons list_data list_dtype
          (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)) =
     Fcons list_data list_dtype  (Fcons list_link (tptr list_struct) Fnil)).
unfold unroll_composite_fields.
f_equal.
change (unroll_composite list_structid list_struct list_dtype = list_dtype).
apply list_unroll_dtype.
rewrite if_true by auto.
f_equal.
rewrite UNROLL.
simpl type_of_field. rewrite if_true by auto.
normalize.
forget (field_mapsto Share.top list_struct list_data x v) as foo.
rewrite (field_mapsto_typecheck_val list_struct list_link sh x tail
                        list_structid 
                    (Fcons list_data list_dtype
                        (Fcons list_link (Tcomp_ptr list_structid noattr)
                           Fnil))  noattr); auto.
rewrite UNROLL. simpl type_of_field.
rewrite if_false by apply list_data_not_link.
rewrite if_true by auto.
normalize.
(***)
intros.
inv H2.
apply exp_right with y.
normalize.
Qed.

Lemma lseg_unroll: forall sh l x z , 
    lseg sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons sh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
normalize.
apply orp_right1; auto.
apply orp_right2.
unfold lseg_cons.
normalize.
apply exp_right with v.
normalize.
apply exp_right with l.
normalize.
apply exp_right with tail.
normalize.
pattern (field_mapsto sh list_struct list_data x v) at 1;
  erewrite (field_mapsto_typecheck_val list_struct list_data sh x v); try reflexivity.
pattern (field_mapsto sh list_struct list_link x tail) at 1;
 erewrite (field_mapsto_typecheck_val list_struct list_link sh x tail); try reflexivity.
normalize.
apply andp_right; auto.
apply andp_right; apply prop_right.
rewrite <- (list_unroll_dtype list_struct).
simpl in H0. rewrite if_true in H0 by auto. apply H0.
simpl in H1. rewrite if_false in H1 by apply list_data_not_link.
rewrite if_true in H1 by auto. rewrite if_true in H1 by auto.
apply H1.
apply orp_left; normalize.
unfold lseg_cons.
normalize. intros. inv H0.
apply orp_left.
normalize. inv H0.
unfold lseg_cons.
normalize.
intros. symmetry in H0; inv H0.
apply exp_right with y.
normalize.
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


Lemma lseg_unroll_nonempty1:
   forall p P sh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    typecheck_val h list_dtype = true ->
    typecheck_val p (tptr list_struct) = true ->
    P |-- field_mapsto sh list_struct list_data v1 h *
             (field_mapsto sh list_struct list_link v1 p *
               lseg sh tail p v2) ->
    P |-- lseg sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H2 | ].
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
 apply now_later.
Qed.

Lemma lseg_nonnull:
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg sh s v nullval = lseg_cons sh s v nullval.
Proof.
intros. subst. 
rewrite lseg_unroll.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
apply orp_right2. auto.
Qed.

Lemma lift2_lseg_cons: 
 forall sh s p q, `(lseg_cons sh s)  p q =
    EX hry:(val * list val * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (`ptr_neq p q) &&
       (`(field_mapsto sh list_struct list_data) p (`h) *
        `(field_mapsto sh list_struct list_link) p (`y) *
        |> `(lseg sh r) (`y) q))
     end.
Proof.
 intros.
 unfold lseg_cons, ptr_neq; unfold_coerce. extensionality rho. simpl.
 apply pred_ext; normalize.
(* destruct s; symmetry in H0; inv H0. *)
 apply exp_right with (h, r, y). normalize.
 destruct h as [[h r] y]. normalize.
 apply exp_right with h. normalize. apply exp_right with r.
 normalize. apply exp_right with y. normalize.
 apply andp_right.
 erewrite (field_mapsto_typecheck_val); [ | reflexivity].
  replace (type_of_field
         (unroll_composite_fields list_structid list_struct
            (Fcons list_data list_dtype
               (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)))
         list_data) with list_dtype.
 forget (field_mapsto sh list_struct list_data (p rho) h ) as A.
 forget (|>lseg sh r y (q rho)) as B.
 erewrite (field_mapsto_typecheck_val); [ | reflexivity].
  replace (type_of_field
         (unroll_composite_fields list_structid list_struct
            (Fcons list_data list_dtype
               (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)))
         list_link) with (tptr list_struct) .
 normalize.
 simpl.
 rewrite if_false by apply list_data_not_link. rewrite if_true by auto.
 rewrite if_true by auto.  reflexivity.
 pose proof (list_unroll_dtype list_struct).
 simpl. rewrite if_true by auto.
 symmetry; apply H0.
 normalize.
Qed.

Lemma unfold_lseg_cons:
   forall P Q1 Q R e sh s,
      local Q1 &&
      PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      local Q1 && PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R))) |--
     EX hry: val * list val * val,
      match hry with (h,r,y) => 
       !! (s=h::r) &&
      PROPx P (LOCALx Q 
        (SEPx (`(field_mapsto sh list_struct list_data) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg sh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(local Q1 && PROPx P (LOCALx Q (SEPx (`(lseg_cons sh s) e (`nullval) :: R)))).
apply derives_trans with
(local Q1 && local (`(typed_true (tptr list_struct)) e) &&
 PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R)))).
apply andp_right; auto.
apply andp_right; auto.
apply andp_left1; auto.
apply andp_left2; auto.
clear H.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue; unfold_coerce; simpl.
normalize.
rewrite lseg_nonnull by auto.
auto.
rewrite lift2_lseg_cons.
clear.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
normalize.
apply exp_right with x;
destruct x as [[h r] y].
normalize.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma semax_lseg_nonnull:
  forall Delta P Q sh s e R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e)  ->
  (forall (h: val) (r: list val) (y: val), s=h::r ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(field_mapsto sh list_struct list_data) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg sh r) (`y) (`nullval) ::
                  R)))) c Post) ->
  semax Delta (PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R)))) c Post.
Proof.
intros.
eapply semax_pre;  [apply unfold_lseg_cons | ].
eapply derives_trans; [ | apply H].
normalize.
apply extract_exists_pre; intros [[h r] y].
apply semax_extract_prop; intro; auto.
Qed.


Lemma lseg_nil_eq: 
    forall sh p q, lseg sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left. normalize.
 normalize. unfold lseg_cons. normalize. inv H0.
 apply orp_right1. normalize.
Qed.
End LIST.

Hint Rewrite @lseg_nil_eq : normalize.

Hint Rewrite @lseg_eq using reflexivity: normalize.



