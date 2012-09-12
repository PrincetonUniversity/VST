Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import compcert.Ctypes.
Require Import progs.client_lemmas.

Local Open Scope logic.

Definition valt := (val * type)%type.

Definition field_of (vt: valt) (fld: ident) : valt :=
 match vt with
 | (Vptr l ofs, Tstruct id fList att) =>
         match field_offset id fList with 
         | Errors.OK delta => (Vptr l (Int.add ofs (Int.repr delta)), type_of_field fList fld)
         | _ => (Vundef, Tvoid)
         end
  | _ => (Vundef, Tvoid)
 end.

Fixpoint fields_mapto (sh: Share.t) (v1: val*type) (flds: list ident) (v2: list (valt)) : mpred :=
  match flds, v2 with
  | nil, nil => emp
  | i::flds', vt::v2' => field_mapsto sh v1 i vt * fields_mapto sh v1 flds' v2'
  | _, _ => FF
  end.

Fixpoint field_names (flds: fieldlist) : list ident :=
  match flds with
  | Fnil => nil
  | Fcons i t flds' => i :: field_names flds'
  end.

Definition struct_fields_mapto (sh: Share.t) (v1: valt) (v2: list (valt)) : mpred :=
  match snd v1 with
  | Tstruct id fList  att =>
         fields_mapto sh v1 (field_names fList) v2
  | _  => FF
  end.

Definition nullval : val := Vint Int.zero.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 => Int.cmpu Ceq n1 n2 = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Int.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

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

Definition mlseg (ls: multilistspec) (sh: share) := 
  HORec (fun (R: (list (list valt))*(val*val) -> mpred) (lp: (list (list valt))*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           fields_mapto sh (first, mlist_struct ls) (mlist_data_fieldnames ls) h 
                           * field_mapsto sh (first, mlist_struct ls) (mlist_link ls) (tail, mlist_type ls)
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Class listspec (t: type) := mk_listspec {
   list_structid: ident;
   list_data: ident;
   list_dtype: type;
   list_link: ident;
   list_struct: type := (Tstruct list_structid 
       (Fcons list_data list_dtype
        (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)) noattr);
   list_type_is: t = Tpointer list_struct noattr;
   list_data_not_link: list_data<>list_link;
   list_unroll_dtype:
              forall T, unroll_composite list_structid T list_dtype = list_dtype;
   list_access_mode: exists ch, access_mode list_dtype = By_value ch
}.

Definition lseg' (T: type) {ls: listspec T} (sh: share) := 
  HORec (fun (R: (list val)*(val*val) -> mpred) (lp: (list val)*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           field_mapsto sh (first, list_struct) list_data (h, list_dtype) 
                           * field_mapsto sh (first, list_struct) list_link (tail, T)
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Definition lseg (T: type) {ls: listspec T} (contents: list val) (x y: val) : mpred :=
   lseg'  T Share.top (contents, (x,y)).

Lemma lseg_unfold (T: type) {ls: listspec T}: forall contents v1 v2,
    lseg T contents v1 v2 = 
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                       field_mapsto Share.top (v1, list_struct) list_data (h, list_dtype) 
                      * field_mapsto Share.top (v1, list_struct) list_link (tail, T)
                      * |> lseg T t tail v2
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

Lemma lseg_eq T {ls: listspec T}:
  forall l v , 
  typecheck_val v T = true ->
    lseg T l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold T l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
unfold typecheck_val in H.
rewrite list_type_is in H.
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
rewrite list_type_is in H.
unfold ptr_eq, typecheck_val in H|-*.
destruct v; inv H; auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
Qed.

Lemma lseg_neq:
  forall T {ls: listspec T} l x z , 
  typecheck_val x T = true ->
  typecheck_val z T = true ->
  ~ptr_eq x z -> 
    lseg T l x z =
         EX h:val, EX r:list val, EX y:val, 
             !!(l=h::r 
                /\ typecheck_val h list_dtype  = true/\ typecheck_val y T = true) && 
             field_mapsto Share.top (x, list_struct) list_data (h, list_dtype) * 
             field_mapsto Share.top (x, list_struct) list_link (y,T) * 
             |> lseg T r y z.
Proof.
intros.
rewrite lseg_unfold at 1; auto.
destruct l.
apply pred_ext; normalize.
intros ? ? ? [? [? ?]]. inv H2.
assert (UNROLL: unroll_composite_fields list_structid list_struct
       (Fcons list_data list_dtype
          (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)) =
     Fcons list_data list_dtype  (Fcons list_link T Fnil)).
unfold unroll_composite_fields.
f_equal.
change (unroll_composite list_structid list_struct list_dtype = list_dtype).
apply list_unroll_dtype.
rewrite if_true by auto.
f_equal.
symmetry. apply list_type_is.
destruct list_access_mode as [ch ACC].
normalize.
apply pred_ext; normalize.
intro y.
rename v into h.
apply (exp_right h).
apply (exp_right l).
apply (exp_right y).
apply sepcon_derives; auto.
normalize.
erewrite (field_mapsto_type list_data); [ | reflexivity].
simpl @snd. normalize.
fold list_struct.
rewrite UNROLL.
unfold type_of_field. rewrite if_true by auto.
erewrite (field_mapsto_typecheck_val list_data) at 1.
erewrite (field_mapsto_typecheck_val list_link) at 1.
simpl.
normalize.
(***)
intros.
destruct H2 as [? [? ?]].
symmetry in H2; inv H2.
rename x2 into y.
apply (exp_right y).
normalize.
Qed.

Module TestCase.
Definition myid : ident := 3%positive.
Definition data_id : ident := 4%positive.
Definition link_id : ident := 5%positive.
Definition Tint32s := Tint I32 Signed noattr.

Definition mylist : type := 
 Tpointer (Tstruct myid (Fcons data_id Tint32s (Fcons link_id (Tcomp_ptr myid noattr) Fnil)) noattr) noattr.

Instance mylist_spec: listspec mylist.
Proof.
econstructor.
reflexivity.
intro Hx; inv Hx.
intros.
unfold unroll_composite; simpl.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Parameters v v' : val.
Parameters x y : val.
Parameter whatever : mpred.
Goal  lseg mylist (x::y::nil) v v' |-- whatever.
rewrite lseg_unfold by auto.
normalize.
intros.
simpl.

Abort.
End TestCase.

(*
DONE TO HERE.
The rest is old stuff from msl/examples/cont/lseg.v

 

Lemma lseg_neq: forall vl p q: valt, 
     is_list_type (snd p) ->
     snd p = snd q ->
    ~ (ptr_eq (fst p) (fst q)) ->
        lseg vl p q = EX h: val, EX vl': list valt, 
                !! (vl = (h,snd p)::vl') && 
              field_mapsto Share.top (deref v1) data h * 
              next link Share.top v1 (tail,snd v1) * |> lseg t (tail, snd v1) v2

next p y *  |> lseg y q.
Proof.
 intros.
 apply pred_ext.
 rewrite lseg_unfold at 1.
 apply orp_left.
 apply andp_left2. apply exp_derives; intro y.
 apply sepcon_derives; auto.
 apply prop_andp_left; contradiction.
 rewrite (lseg_unfold p q). apply orp_right1.
 apply prop_andp_right; auto.
Qed.

Lemma lseg_eq: forall a, lseg a a = emp.
Proof.
 intros. rewrite lseg_unfold.
 apply pred_ext.
 apply orp_left.
 apply prop_andp_left; congruence.
 apply prop_andp_left; auto.
 apply orp_right2. apply prop_andp_right; auto. 
Qed.

Lemma lseg_cons: (* U2 *)
 forall x y z, x<>z -> next x y * lseg y z |-- lseg x z.
Proof.
 intros.
 pattern lseg at 1; rewrite lseg_unfold.
 apply orp_right1.
 apply prop_andp_right; auto.
 apply exp_right with y.
 apply sepcon_derives; auto.
 unfold lseg.
 apply now_later.
Qed.

Lemma lseg_neq_0:  forall y, lseg 0 y |-- !! (y=0).  (* W2 *)
Proof.
  intros. 
  rewrite lseg_unfold.
 apply orp_left.
 apply andp_left2.
 apply exp_left; intro v.
 rewrite next_gt_0.
 rewrite sepcon_andp_prop1.
 apply prop_andp_left; intro. inv H.
 apply andp_left1.
 intros w ?; hnf in *; auto.
Qed.

Lemma next_lseg:  (* U1 *)
  forall x y, x<>y ->  next x y |-- lseg x y.
Proof.
  intros.
  rewrite <- (sepcon_emp (next x _)).
  rewrite <- (lseg_eq y).
  eapply derives_trans; [ apply lseg_cons | ]; auto.
Qed.


Lemma mapsto_conflict:
   forall a b c, mapsto a b  *  mapsto a c |-- FF.
  Proof.
    intros. intros w  [w1 [w2 [? [? ?]]]]; hnf.
    specialize (H0 a). specialize (H1 a).
    rewrite if_true in * by auto.
    apply (resource_at_join _ _ _ a) in H.
    rewrite H0 in H; rewrite H1 in H; inv H.
    pfullshare_join.
 Qed.

Lemma next_conflict:  (*  W3 *)
   forall x y y', next x y * next x y' |-- FF.
Proof.
  unfold next; intros.
  eapply derives_trans; [ | apply (mapsto_conflict x y y')].
  apply sepcon_derives; apply andp_left2; auto.
Qed.

Lemma not_prop_right: forall P (Q: Prop), (Q -> P |-- FF) -> P |-- !! (not Q).
 Proof. intros. intros w ? ?. specialize (H H1 w H0); auto. 
  Qed.

 Lemma next_conflict_list: (* W4 *)
     forall x y z, next x y * lseg z 0 |-- !!(x<>z).
 Proof.
   intros.
   unfold next.
   rewrite lseg_unfold.
  rewrite sepcon_comm.
  rewrite distrib_orp_sepcon.
  apply orp_left.
  repeat rewrite sepcon_andp_prop1. 
  apply andp_left2.
  rewrite exp_sepcon1.
  apply exp_left; intro v. 
  rewrite sepcon_comm.
  rewrite <- sepcon_assoc.
  apply @derives_trans with (!! (x<>z) && TT * TT).
  apply sepcon_derives; auto.
  apply andp_right; auto. 
  apply not_prop_right; intros; subst; apply next_conflict.
  rewrite sepcon_andp_prop1.
  apply andp_left1; auto.
  rewrite sepcon_andp_prop1. rewrite emp_sepcon.
  apply prop_andp_left; intro.
  subst.
  unfold next.
  apply prop_andp_left; intro.
  intros ? ?; hnf; omega.
Qed.

Lemma lseg_W5: forall x y z,   (* W5 *)
    lseg x y * lseg x z |-- !!(x=y \/ x=z).
Proof.
  intros.
  destruct (eq_dec x y).
  apply prop_right; auto.
  destruct (eq_dec x z).
  apply prop_right; auto.
  rewrite (lseg_neq x y); auto.
  rewrite exp_sepcon1; apply exp_left; intro.
  rewrite (lseg_neq x z); auto.
  rewrite exp_sepcon2; apply exp_left; intro.
  rewrite sepcon_assoc. 
  rewrite <- (sepcon_assoc (|> _)).
  rewrite (sepcon_comm (|> _)).
  repeat rewrite <- sepcon_assoc. rewrite sepcon_assoc.
  eapply derives_trans. apply sepcon_derives. apply next_conflict. apply derives_refl.
  rewrite FF_sepcon. auto.
Qed.

(* This lemma is not currently used, 
    but it might be useful in a different proof of lseg_cons_in_mapsto_context, etc. *)
Lemma sepcon_andp_fash'1 {A}{JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:  
    forall (P: pred nat) (Q R : pred A),  fash' P && Q * R = fash' P && (Q * R).
 Proof.
  intros. apply pred_ext; intros w ?.
   destruct H as [w1 [w2 [? [? ?]]]].
   destruct H0. split.
   hnf in H0|-*. replace (level w) with (level w1); auto.
   apply join_level in H; intuition.
    exists w1; exists w2; split3; auto.
   destruct H.
   destruct H0 as [w1 [w2 [? [? ?]]]]; exists w1; exists w2; split3; auto.
   split; auto.
   hnf in H|-*. replace (level w1) with (level w); auto.
   apply join_level in H0; intuition.
Qed.

Lemma lseg_cons_in_next_context:   (*  U4 *)
    forall x y z v, lseg x y * next y z * next z v |-- lseg x z * next z v.
Proof.
  intros.
  apply @derives_trans with ((lseg x y * next y z) && (ewand (next z v) TT) *  next z v).
  intros w [w1 [w2 [? [ ? ?]]]]. exists w1; exists w2; split3; auto. split; auto.
  exists w2; exists w; split3; auto.
  apply sepcon_derives; auto.
  generalize (goedel_loeb (ALL x:adr,  
    lseg x y * next y z && ewand (next z v) TT >=> lseg x z) TT) ; intro.
  spec H.
  2:  intros w ?; apply (H (@level _ R.ag_rmap w) I x w (le_refl _)); auto.
  clear.
  apply allp_right; intro x.
  apply subp_i1.
  intros w [[_ ?] [? ?]].
  rewrite lseg_unfold. left.
  split.
  do 3 red. intro; subst x.
  clear - H0 H1.
  destruct H1 as [w1 [w2 [? [? _]]]].
  assert (app_pred (next z v * (lseg z y * next y z)) w2) by (do 2 eexists; split3; eauto).
  rewrite <- sepcon_assoc in H2.
  destruct H2 as [wa [wb [? [? ?]]]].
  assert (app_pred (lseg z y * (next y z * next z v)) w2).
  rewrite sepcon_comm.
  rewrite sepcon_assoc.
  exists wb; exists wa; split3; auto.
  clear - H5.
  rewrite (lseg_unfold z y) in H5.
  rewrite distrib_orp_sepcon in H5.
  destruct H5.
  repeat rewrite sepcon_andp_prop1 in H.
  destruct H as [_ H].
  repeat rewrite exp_sepcon1 in H.
  destruct H as [u ?].
  rewrite (sepcon_comm (next z u)) in H.
  rewrite sepcon_assoc in H.
  rewrite sepcon_comm in H.
  rewrite (sepcon_comm (next y z)) in H.
  rewrite <- sepcon_assoc in H.
  rewrite sepcon_assoc in H.
  destruct H as [w1 [w3 [? [? _]]]].
  apply next_conflict in H0; auto.
  rewrite sepcon_andp_prop1 in H. rewrite emp_sepcon in H.
  destruct H. hnf in H. subst y.
  apply next_conflict in H0; auto.
  rewrite lseg_unfold in H0.
  rewrite distrib_orp_sepcon in H0.
  destruct H0.
  repeat rewrite sepcon_andp_prop1 in H0.
  destruct H0.
  repeat rewrite exp_sepcon1 in H2.
  destruct H2 as [u H2].
  do 3 red in H0. exists u.
 rewrite later_allp in H.
  specialize (H u).
  rewrite sepcon_assoc in H2.
  destruct H2 as [w1 [w2 [? [? ?]]]].
  red in H. rewrite subp_later in H.
  specialize (H w2).
  spec H. apply join_level in H2; destruct H2; omega.
  exists w1; exists w2; split3; auto.
  apply H; auto.
  rewrite later_andp. split.
  rewrite later_sepcon.
  eapply sepcon_derives; try apply H4; auto.
  apply now_later.
  eapply now_later; eauto.
  clear - H2 H1.
  destruct H1 as [w3 [w4 [? [? _]]]].
  destruct (join_assoc H2 (join_comm H)) as [f [? ?]].
  exists w3; exists f; split3; auto.
  exists z.
  rewrite lseg_eq.
  rewrite sepcon_andp_prop1 in H0.
  destruct H0. hnf in H0; subst y.
  rewrite sepcon_comm in H2.
  eapply sepcon_derives; try apply H2; auto.
  apply now_later.
Qed.

Lemma list_append:  (* U3 *)
   forall x y, lseg x y * lseg y 0 |-- lseg x 0.
Proof.
 intros.
  generalize (goedel_loeb (ALL x:adr, lseg x y * lseg y 0  >=> lseg x 0) TT) ; intro.
  spec H; [ clear  | intros w ?; apply (H (@level _ R.ag_rmap w) I x w (le_refl _)); auto].
  apply andp_left2.
  apply allp_right; intro x.
  apply subp_i1.
  intros w [? ?].
  destruct (eq_dec x 0).
  subst. rewrite lseg_eq.
  rewrite lseg_unfold in H0.
  rewrite distrib_orp_sepcon in H0.
  destruct H0.
  rewrite sepcon_andp_prop1 in H0. destruct H0.
  rewrite exp_sepcon1 in H1.
  destruct H1 as [u ?]. unfold next in H1.
  repeat rewrite sepcon_andp_prop1 in H1.
  destruct H1 as [H1 _]; hnf in H1. inv H1. 
  rewrite sepcon_andp_prop1 in H0. destruct H0. hnf in H0. subst.
  rewrite lseg_eq in H1. rewrite sepcon_emp in H1. auto.
  rewrite (lseg_unfold x y) in H0.
  rewrite distrib_orp_sepcon in H0.
  destruct H0.
  rewrite sepcon_andp_prop1 in H0. destruct H0.
  rewrite exp_sepcon1 in H1.
  destruct H1 as [z H1].
  rewrite lseg_neq; auto.
  exists z.
  rewrite sepcon_assoc in H1.
  rewrite later_allp in H.
  specialize (H z).
  destruct H1 as [w1 [w2 [? [? ?]]]].
  red in H. rewrite subp_later in H.
  specialize (H w2).
  spec H. apply join_level in H1; destruct H1; omega.
  exists w1; exists w2; split3; auto.
  apply H; auto.
  rewrite later_sepcon.
  eapply sepcon_derives; try apply H3; auto.
  apply now_later.
  rewrite sepcon_andp_prop1 in H0.
  destruct H0. hnf in H0; subst y. rewrite emp_sepcon in H1; auto.
Qed.

Lemma lseg_U5:
    forall x y z w, z<>w -> lseg x y * next y z * lseg z w |-- lseg x z * lseg z w.
Proof.
 intros.
 rewrite (lseg_neq z w); auto.
 repeat rewrite exp_sepcon2.
 apply exp_derives; intro v.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives; auto.
 apply lseg_cons_in_next_context.
Qed.

Lemma lseg_cons_in_list_context: 
    forall x y z, lseg x y * next y z * lseg z 0 |-- lseg x z * lseg z 0.
Proof.
  intros.
  destruct (eq_dec z 0).
  subst. rewrite lseg_eq. repeat  rewrite sepcon_emp. 
  eapply derives_trans; try apply list_append.
  apply sepcon_derives; eauto.
  rewrite next_gt_0.
  apply prop_andp_left; intro.
  apply next_lseg; omega.
  apply lseg_U5; auto.
Qed.

*)