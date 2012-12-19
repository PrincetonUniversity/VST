Load loadpath.
Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.list.

Local Open Scope logic.

Require progs.test1.
Module P := progs.test1.

Local Open Scope logic.

Instance t_list_spec: listspec P.t_listptr.
Proof.
econstructor.
reflexivity.
intro Hx; inv Hx.
intros.
unfold unroll_composite; simpl.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Definition ilseg (sh: share) (s: list int) := lseg P.t_listptr sh (map Vint s).

Definition ilseg_nil (l: list  int) x z : mpred := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons (sh: share) (s: list int) := lseg_cons P.t_listptr sh (map Vint s).

Lemma ilseg_unroll: forall sh l x z , 
    ilseg sh l x z = ilseg_nil l x z || ilseg_cons sh l x z.
Proof.
intros.
unfold ilseg at 1.
rewrite lseg_unroll.
unfold ilseg_cons, ilseg_nil, ilseg.
f_equal.
f_equal. f_equal.
f_equal.
apply prop_ext; split; intro; destruct l; simpl in *; congruence.
Qed.

Lemma ilseg_eq: forall sh s p, 
   typecheck_val p P.t_listptr = true -> 
    (ilseg sh s p p = !!(s=nil) && emp).
Proof. intros. unfold ilseg. rewrite lseg_eq; auto. f_equal. f_equal.
 apply prop_ext. destruct s; simpl; intuition congruence.
Qed.
Hint Rewrite ilseg_eq : normalize.

Lemma ilseg_nonnull:
  forall sh s v,
      typed_true P.t_listptr v ->
     ilseg sh s v nullval = ilseg_cons sh s v nullval.
Proof.
intros. subst. 
rewrite ilseg_unroll.
unfold ilseg_cons, ilseg_nil.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
intros.
normalize.
apply orp_right2.
assert (~ ptr_eq v nullval).
intro. unfold typed_true,ptr_eq in *. destruct v; simpl in *; auto.
rewrite H0 in H; inv H.
normalize.
Qed.

Lemma ilseg_nil_eq: forall sh p q, ilseg sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite ilseg_unroll.
 apply pred_ext.
 apply orp_left.
 unfold ilseg_nil.  normalize.
 unfold ilseg_cons. normalize. unfold lseg_cons. normalize. intros. inv H0.
 apply orp_right1. unfold ilseg_nil. normalize.
Qed.
Hint Rewrite ilseg_nil_eq : normalize.

Lemma lift2_ilseg_cons: 
 forall sh s p q, lift2 (ilseg_cons sh s)  p q =
    EX hry:(int * list int * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (lift2 ptr_neq p q) &&
       (lift2 (field_mapsto sh list_struct list_data) p (lift0 (Vint h)) *
        lift2 (field_mapsto sh list_struct list_link) p (lift0 y) *
        |> lift2 (ilseg sh r) (lift0 y) q))
     end.
Proof.
 intros.
 unfold ilseg_cons, lseg_cons, lift2. extensionality rho. simpl.
 unfold local, lift1. unfold ptr_neq.
 unfold ilseg.
 apply pred_ext; normalize.
 destruct s; symmetry in H0; inv H0.
 apply exp_right with (i, s, y). normalize.
 destruct h as [[h r] y]. normalize.
 apply exp_right with (Vint h). normalize. apply exp_right with (map Vint r).
 normalize. apply exp_right with y. normalize.
 apply andp_right.
 forget (field_mapsto sh list_struct P.i_h (p rho) (Vint h) ) as A.
 forget (|>lseg P.t_listptr sh (map Vint r) y (q rho)) as B.
 erewrite (field_mapsto_typecheck_val); try reflexivity.
 normalize.
 apply prop_right.
 replace P.t_listptr with (type_of_field
         (unroll_composite_fields list_structid list_struct
            (Fcons list_data list_dtype
               (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)))
         P.i_t); auto.
 type_of_field_tac.
 normalize.
Qed.

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH sh_contents 
  PRE [ P.i_p : P.t_listptr]  lift2 (ilseg (fst sh_contents) (snd sh_contents)) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_int ]  local (lift1 (eq (Vint (fold_right Int.add Int.zero (snd sh_contents)))) retval).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH sh_contents : share * list int
  PRE  [ P.i_p : P.t_listptr ] !! writable_share (fst sh_contents) &&
        lift2 (ilseg (fst sh_contents) (snd sh_contents)) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_listptr ] lift2 (ilseg (fst sh_contents) (rev (snd sh_contents))) retval (lift0 nullval).

Definition main_spec :=
 DECLARE P.i_main
  WITH u : unit
  PRE  [] main_pre P.prog u
  POST [ P.t_int ] main_post P.prog u.

Definition main_spec' := (P.i_main, mk_funspec (nil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Vprog : varspecs := (P.i_three, Tarray P.t_list 3 noattr)::nil.

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (sh: share) (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL (lift1 (partial_sum contents cts) (eval_id P.i_s)) 
            SEP (TT * lift2 (ilseg sh cts) (eval_id P.i_t) (lift0 nullval))).

Ltac start_function :=
match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
  match Pre with fun i => _ => intro i end;
  simpl fn_body; simpl fn_params; simpl fn_return;
  canonicalize_pre
 end.


Opaque sepcon.
Opaque emp.
Opaque andp.


Lemma eval_expr_binop: forall op a1 a2 t, eval_expr (Ebinop op a1 a2 t) = 
          lift2 (eval_binop op (typeof a1) (typeof a2)) (eval_expr a1)  (eval_expr a2).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_binop : normalize.

Lemma eval_expr_unop: forall op a1 t, eval_expr (Eunop op a1 t) = 
          lift1 (eval_unop op (typeof a1)) (eval_expr a1).
Proof. reflexivity. Qed.
Hint Rewrite eval_expr_unop : normalize.

Lemma body_sumlist: semax_body Vprog Gprog P.f_sumlist sumlist_spec.
Proof.
start_function.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
forward.
forward.
forward_while (sumlist_Inv sh contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P.i_s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv, partial_sum.
apply exp_right with contents.
go_lower.
rewrite H0. rewrite H1.
rewrite Int.add_zero_l. normalize.
rewrite sepcon_comm.
apply sepcon_TT.
(* Prove that loop invariant implies typechecking condition *)
intro; apply TT_right.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv, partial_sum.
go_lower. intros.  rewrite H0.
rewrite (typed_false_ptr H).
normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
autorewrite with normalize.
apply extract_exists_pre; intro cts.
autorewrite with normalize.
replace_in_pre (ilseg sh cts) (ilseg_cons sh cts).
rewrite ilseg_nonnull; auto.
rewrite lift2_ilseg_cons.
normalizex. intros [[h r] y].
normalizex. subst cts.
simpl list_data; simpl list_link.
forward. normalize.
forward.  intro old_t.
forward.
(* Prove postcondition of loop body implies loop invariant *)
intro x; unfold sumlist_Inv, partial_sum.
apply exp_right with r.
go_lower.
autorewrite with normalize in H0.
rewrite H0. rewrite H4. clear H4. rewrite H1. clear H1.
assert (H1: tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
destruct (tc_val_extract_int _ _ _ _ H1) as [n H4].
rewrite H4 in *.
destruct x; inv H0.
simpl. rewrite (Int.add_assoc i h). normalizex.
rewrite <- (sepcon_comm TT).
repeat rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
normalize.
(* After the loop *)
forward.
go_lower.
apply andp_right; normalize.
eapply tc_eval_id_i; eauto.
rewrite H0.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
destruct (eval_id P.i_s rho); inv H1; auto.
unfold retval; simpl. normalize.
Qed.

Definition reverse_Inv (sh: share) (contents: list int) : assert :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (lift2 (ilseg sh cts1) (eval_id P.i_w) (lift0 nullval) *
                   lift2 (ilseg sh cts2) (eval_id P.i_v) (lift0 nullval))).

Lemma body_reverse: semax_body Vprog Gprog P.f_reverse reverse_spec.
Proof.
start_function.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
normalizex. rename H into WS.
forward.
go_lower.
forward.
forward_while (reverse_Inv sh contents)
         (PROP() LOCAL () SEP( lift2 (ilseg sh (rev contents)) (eval_id P.i_w) (lift0 nullval))).
(* precondition implies loop invariant *)
unfold reverse_Inv.
go_lower.
apply exp_right with nil. normalize.
apply exp_right with contents. normalize.
rewrite H0. rewrite H1.
simpl; normalize. 
(* loop invariant implies typechecking of loop condition *)
normalizex.
(* loop invariant (and not loop condition) implies loop postcondition *)
unfold reverse_Inv.
go_lower. intro cts2.
rewrite (typed_false_ptr H). 
normalize.
rewrite <- app_nil_end. rewrite rev_involutive. auto.
(* loop body preserves invariant *)
unfold reverse_Inv at 1.
normalize.
apply extract_exists_pre; intro cts.
normalize.
apply extract_exists_pre; intro cts2.
normalizex. subst contents.
replace_in_pre (ilseg sh cts2) (ilseg_cons sh cts2).
rewrite (ilseg_nonnull sh cts2) by auto. auto.
rewrite lift2_ilseg_cons.
normalizex. intros [[h r] y].
normalizex; subst cts2.
simpl list_data; simpl list_link.
forward. normalize.
forward. normalize.
forward. intro old_w.
forward.
intros.
unfold reverse_Inv.
go_lower.
apply exp_right with (h::cts).
apply exp_right with r.
normalize. 
simpl. rewrite app_ass.
simpl.
normalize.
rewrite (ilseg_unroll sh (h::cts)).
apply derives_trans with (ilseg_cons sh (h :: cts) (eval_id P.i_w rho) nullval *
    ilseg sh r (eval_id P.i_v rho) nullval).
unfold ilseg_cons, lseg_cons.
normalize. apply exp_right with (Vint h).
normalize. apply exp_right with (map Vint cts).
normalize. apply exp_right with old_w.
normalize. rewrite H0.
simpl list_data; simpl list_link.
repeat rewrite <- sepcon_assoc.
erewrite (field_mapsto_typecheck_val _ _ _ _ _ P.i_list _  noattr); [ | reflexivity].
type_of_field_tac.
normalize.
assert (eval_cast P.t_listptr P.t_listptr old_w = old_w)
  by (destruct old_w ; inv H3; simpl; auto).
rewrite H4 in *.
normalize.
repeat pull_right (field_mapsto sh P.t_list P.i_t (eval_id P.i_w rho) old_w).
apply sepcon_derives; auto.
repeat pull_right (field_mapsto sh list_struct P.i_h (eval_id P.i_w rho) (Vint h)).
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
apply now_later.
apply sepcon_derives; auto.
apply orp_right2; auto.
(* after the loop *)
forward.
go_lower.
apply andp_right; normalize.
apply prop_right.
eapply tc_eval_id_i; eauto.
unfold retval; normalize.
Qed.

Lemma cast_redundant:
  forall e t, cast_exp (Ecast e t) t = cast_exp e t.
Proof. intros. extensionality rho; unfold cast_exp; simpl.
unfold lift1. unfold expr.eval_cast.
f_equal.
forget (eval_expr e rho) as v.
forget (typeof e) as t0.
Admitted.

Lemma cast_exp_pointer:
  forall e t t', typeof e = Tpointer t noattr -> 
                         t' = Tpointer t noattr ->
                    cast_exp e t' = eval_expr e.
Admitted.

  Lemma eval_cast_pointer:
   forall  t1 t v,
       match t1, t with (Tpointer _ _), (Tpointer _ _) => True | _,_ => False end ->
       tc_val t1 v ->
       eval_cast t1 t v = v.
 Proof. intros. destruct t1; try contradiction. destruct t; try contradiction.
  unfold eval_cast. unfold Cop.sem_cast. simpl in *.
  unfold tc_val, typecheck_val in H0. destruct v; auto; inv H0.
Qed.

Lemma tc_eval_gvar_i:
  forall Delta t i rho, tc_environ Delta rho ->
            (var_types Delta) ! i = None ->
            (glob_types Delta) ! i = Some (Global_var t) ->
             tc_val (Tpointer t noattr) (eval_var i t rho).
Proof.
 intros. unfold tc_val, eval_var; simpl.
 hnf in H. unfold typecheck_environ in H.
 repeat rewrite andb_true_iff in H.
  destruct H as [[[_ ?] ?] ?].
  apply environ_lemmas.typecheck_mode_eqv in H3.
  apply environ_lemmas.typecheck_ge_eqv in H2.
  apply environ_lemmas.typecheck_ve_eqv in H.
  destruct (H3 _ _ H1).
  unfold Map.get; rewrite H4.
  destruct (H2 _ _ H1) as [b [i' [? ?]]].
   rewrite H5. simpl. rewrite eqb_type_refl.
   simpl globtype in H6.
   auto. 
  destruct H4; congruence.
Qed.

Lemma tc_eval_var_nonnull:
  forall Delta t i rho z, tc_environ Delta rho ->
      match (var_types Delta) ! i with Some _ => True | None =>
               match   (glob_types Delta) ! i with Some _ => True | None => False end
      end ->
      ~ptr_eq (eval_var i t rho) (Vint z).
Admitted.

Definition Ews (* extern_write_share *) := Share.splice extern_retainer Share.top.

Lemma cast_exp_pointer2:
  forall e t1 t2 t', typeof e = Tpointer t1 noattr -> 
                         t' = Tpointer t2 noattr ->
                    cast_exp e t' = eval_expr e.
Admitted.

Lemma globvar_lem1:
  forall (ge: Genv.t fundef type) Delta rho id t,
      tc_environ Delta rho ->
     (var_types Delta) ! id = None ->
     (glob_types Delta) ! id = Some  (Global_var t) ->
     exists b, exists z,  ve_of rho id = None /\ ge_of rho id = Some (Vptr b z, t).
Proof.
intros.
unfold tc_environ, typecheck_environ in H.
repeat rewrite andb_true_iff in H. destruct H as [[[Ha Hb] Hc] Hd].
apply environ_lemmas.typecheck_ge_eqv in Hc. 
hnf in Hc.
specialize (Hc _ _ H1). destruct Hc as [b [i [Hc Hc']]].
exists b; exists i; rewrite Hc.
split; auto.
apply environ_lemmas.typecheck_mode_eqv in Hd.
apply Hd in H1. 
destruct H1; auto. destruct H; simpl in H. congruence.
Qed.

Lemma globvar2pred_lem1:
  forall (ge: Genv.t fundef type) Delta rho id gv t,
      tc_environ Delta rho ->
     (glob_types Delta) ! id = Some  (Global_var t) ->
     gvar_info gv = t ->
     gvar_volatile gv = false ->
      globvar2pred ge (id,gv) rho |--
        EX b:_, EX z:_,  init_data_list2pred ge (gvar_init gv)
                           (readonly2share (gvar_readonly gv)) b (Int.unsigned z)
                 (ge_of rho).
Proof.
intros.
unfold globvar2pred.
simpl @fst; simpl @snd. subst t.
unfold tc_environ, typecheck_environ in H.
repeat rewrite andb_true_iff in H. destruct H as [[[Ha Hb] Hc] Hd].
apply environ_lemmas.typecheck_ge_eqv in Hc. 
hnf in Hc.
specialize (Hc _ _ H0). destruct Hc as [b [i [Hc Hc']]]. rewrite Hc.
rewrite H2.
apply exp_right with b; apply exp_right with i; auto.
Qed.
Lemma address_field_mapsto:
  forall ch v rsh sh b z' z ofs structid fld fields,
  access_mode
        (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) = By_value ch ->
  z' =  (Int.unsigned z + ofs)  mod Int.modulus ->
  field_offset fld fields = Errors.OK ofs ->
  (typecheck_val v
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = true)  ->
  (type_is_volatile
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = false) ->
  address_mapsto ch v rsh sh (b, z') |--
  field_mapsto (Share.splice rsh sh) (Tstruct structid fields noattr) fld (Vptr b z) v.
Proof.
 intros.
 Transparent field_mapsto. unfold field_mapsto.
  simpl. rewrite field_offset_unroll. rewrite H1. rewrite H.
  normalize.
  subst.
 rewrite Zplus_mod_idemp_r. 
 rewrite Share.unrel_splice_L. rewrite Share.unrel_splice_R.
 auto. Opaque field_mapsto.
Qed.

Lemma setup_globals:
  forall rho,  tc_environ (func_tycontext P.f_main Vprog Gprog) rho ->
   main_pre P.prog tt rho
   |-- ilseg Ews (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)
      (cast_exp
         (Ecast
            (Eaddrof (Evar P.i_three (Tarray P.t_list 3 noattr))
               (Tpointer (Tarray P.t_list 3 noattr) noattr)) P.t_listptr)
         P.t_listptr rho) nullval * fold_right sepcon emp nil rho.
Proof.
 unfold main_pre.
 go_lower.
 destruct (globvar_lem1 (Genv.globalenv P.prog) _ _ P.i_three _ H (eq_refl _) (eq_refl _)) 
    as [b [z [H98 H99]]]. simpl in H99.
 assert (H97: eval_var P.i_three (Tarray P.t_list 3 noattr) rho = Vptr b z).
  unfold eval_var. unfold Map.get. rewrite H98; rewrite H99. rewrite eqb_type_refl; auto.
 unfold P.prog, globvars2pred. simpl.
  unfold globvar2pred.
 normalize. simpl. rewrite H99.
   unfold ilseg.
  rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp.
Focus 2.
  erewrite cast_exp_pointer by reflexivity.
  normalize. simpl eval_cast.
 rewrite eval_cast_pointer; simpl; auto; try solve [eapply tc_eval_gvar_i; eauto].
 eapply tc_eval_var_nonnull; eauto.  compute; auto.
  (* End Focus 2 *)
  apply exp_right with (Vint (Int.repr 1)).
  apply exp_right with (Vint (Int.repr 2)::Vint (Int.repr 3)::nil).
  apply exp_right with (eval_expr (Ebinop Cop.Oadd 
                                    (Eaddrof (Evar P.i_three (Tarray P.t_list 3 noattr)) P.t_listptr)
                                    (Econst_int (Int.repr 1) P.t_int)  P.t_listptr) rho).
 simpl. normalize.
 rewrite prop_true_andp.
2:   admit.  (* typechecking proof *)
  rewrite sepcon_assoc.
  apply sepcon_derives.
 erewrite cast_exp_pointer2; [ | reflexivity | reflexivity].
 normalize. 
 erewrite eval_cast_pointer; [ | compute; auto| eapply tc_eval_gvar_i; eauto ].
 simpl eval_expr. rewrite H97.
 unfold list_struct.
 apply address_field_mapsto with 0; simpl; try solve [rewrite if_true; auto].
 admit.  (* easy *)
 unfold field_offset. simpl. rewrite if_true; auto.
 apply sepcon_derives.
 erewrite cast_exp_pointer2; [ | reflexivity | reflexivity].
 normalize. 
 erewrite eval_cast_pointer; [ | compute; auto| eapply tc_eval_gvar_i; eauto ].
 simpl eval_expr.  rewrite H97.
 apply address_field_mapsto with 4; simpl;
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit.  (* perhaps provable from structure of initializers *)
 unfold field_offset. simpl.
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.

  eapply derives_trans; [ | apply now_later].
  rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp.
  2: admit.  (* like the one above *)
  apply exp_right with (Vint (Int.repr 2)).
  apply exp_right with (Vint (Int.repr 3)::nil).
  apply exp_right with (eval_expr (Ebinop Cop.Oadd 
                                    (Eaddrof (Evar P.i_three (Tarray P.t_list 3 noattr)) P.t_listptr)
                                    (Econst_int (Int.repr 2) P.t_int)  P.t_listptr) rho).
 simpl. normalize.
 rewrite prop_true_andp.
2:   admit.  (* typechecking proof *)
  rewrite sepcon_assoc.
  apply sepcon_derives.  rewrite H97.
 unfold eval_binop. simpl. repeat rewrite Zmax_spec; simpl.
 unfold align. simpl.
  rewrite Int.mul_signed. repeat rewrite Int.signed_repr. simpl.
 apply address_field_mapsto with 0; simpl; try solve [rewrite if_true; auto].
  admit.  (* perhaps provable from structure of initializers *)
 unfold field_offset. simpl.
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit.  (* easy *)
 admit.  (* easy *)
  apply sepcon_derives.  rewrite H97.
 unfold eval_binop. simpl. repeat rewrite Zmax_spec; simpl.
 unfold align. simpl.
  rewrite Int.mul_signed. repeat rewrite Int.signed_repr. simpl.
 apply address_field_mapsto with 4; simpl;
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit. 
 unfold field_offset. simpl.
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit.  (* easy *)
 admit.  (* easy *)
  eapply derives_trans; [ | apply now_later].
  rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp.
  2: admit.  (* like the one above *)
  apply exp_right with (Vint (Int.repr 3)).
  apply exp_right with (nil).
  apply exp_right with nullval.
 simpl. normalize.
 match goal with |- ?A |-- sepcon ?B ?C => apply derives_trans with (B*emp) end.
 rewrite sepcon_emp.
  apply sepcon_derives. rewrite H97.
 unfold eval_binop. simpl. repeat rewrite Zmax_spec; simpl.
 unfold align. simpl.
  rewrite Int.mul_signed. repeat rewrite Int.signed_repr. simpl.
 apply address_field_mapsto with 0; simpl; try solve [rewrite if_true; auto].
  admit.  (* perhaps provable from structure of initializers *)
 unfold field_offset. simpl.
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit.  (* easy *)
 admit.  (* easy *)
 rewrite H97.
 unfold eval_binop. simpl. repeat rewrite Zmax_spec; simpl.
 unfold align. simpl.
  rewrite Int.mul_signed. repeat rewrite Int.signed_repr. simpl.
 apply address_field_mapsto with 4; simpl;
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit. 
 unfold field_offset. simpl.
   repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; auto.
 admit.  (* easy *)
 admit.  (* easy *)
  apply sepcon_derives; auto.
  eapply derives_trans; [ | apply now_later].
  rewrite lseg_unroll. apply orp_right1.
  rewrite prop_true_andp. normalize.
  unfold ptr_eq. simpl. rewrite Int.eq_true; auto.
Qed.

Lemma writable_Ews: writable_share Ews.
Admitted.
Hint Resolve writable_Ews.

Lemma body_main:  semax_body Vprog Gprog P.f_main main_spec.
Proof.
start_function.
normalize.
forward. 
go_lower. unfold F,x.
instantiate (2:= (Ews, Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)).
instantiate (1:=nil).
rewrite prop_true_andp by (compute; intuition).
rewrite prop_true_andp by auto.
destruct u; apply setup_globals; auto.
unfold x,F in *; clear x F.
apply extract_exists_pre; normalize.
forward.
go_lower. 
unfold x,F.
instantiate (2:= (Ews, Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil)).
instantiate (1:=nil).
normalize.
rewrite prop_true_andp by (compute; auto).
erewrite cast_exp_pointer by reflexivity.
normalize.
apply extract_exists_pre; intro old.
normalize. clear old.
forward.
go_lower.
eapply tc_eval_id_i; eauto.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
unfold prog_funct; simpl prog_defs.
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

