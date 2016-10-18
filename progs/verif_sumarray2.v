Require Import floyd.proofauto. (* Import the Verifiable C system *)
Require Import progs.sumarray2. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(* Some definitions relating to the functional spec of this particular program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.
  
Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; omega.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed;
                     Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs := 
      augment_funspecs prog [sumarray_spec; main_spec].

(* Loop invariant, for use in body_sumarray.  *)
Definition sumarray_Inv a0 sh contents size := 
 EX i: Z,
   PROP  ((*0 <= i <= size*))
   LOCAL (temp _a a0; 
          (*temp _i (Vint (Int.repr i)); *)
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tint size) (map Vint (map Int.repr contents)) a0).

(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.  (* Always do this at the beginning of a semax_body proof *)
(* The next two lines do forward symbolic execution through
   the first two executable statements of the function body *)
forward.  (* s = 0; *)


Inductive Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is : Type -> Prop := .
Inductive Type_of_bound_in_forward_for_should_be_Z_but_is : Type -> Prop := .

Ltac forward_for_simple_bound n Pre :=
  check_Delta;
 repeat match goal with |-
      semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      apply -> seq_assoc; abbreviate_semax
 end;
 first [ 
    match type of n with
      ?t => first [ unify t Z | elimtype (Type_of_bound_in_forward_for_should_be_Z_but_is t)]
    end;
    match type of Pre with
      ?t => first [unify t (environ -> mpred); fail 1 | elimtype (Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is t)]
    end
  | simple eapply semax_seq'; 
    [forward_for_simple_bound' n Pre 
    | cbv beta; simpl update_tycon; abbreviate_semax  ]
  | eapply semax_post_flipped'; 
     [forward_for_simple_bound' n Pre 
     | ]
  ].

forward_for_simple_bound size (sumarray_Inv a sh contents size).
* (* Prove that current precondition implies loop invariant *)
entailer!.
* (* Prove postcondition of loop body implies loop invariant *)
forward. (* x = a[i] *)
entailer!. (* This is an example of a typechecking condition 
   that is nontrivial; entailer! leaves a subgoal.  The subgoal basically
   says that the array-subscript index is in range;  not just in 
   the bounds of the array, but in the _initialized_ portion of the array.*)
   rewrite Znth_map with (d':=Int.zero). hnf; auto.
   rewrite Zlength_map in H1; auto.
forward. (* s += x; *)
entailer!.
 autorewrite with sublist in *.
 rewrite Znth_map with (d':=Int.zero) by (autorewrite with sublist; omega).
 rewrite Znth_map with (d':=0) by  (autorewrite with sublist; omega).
 simpl. 
 rewrite add_repr.
 f_equal. f_equal.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite sum_Z_app. rewrite (sublist_one i) with (d:=0) by omega.
 simpl. rewrite Z.add_0_r. reflexivity.
* (* After the loop *)
forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
simpl.
apply prop_right.
autorewrite with sublist.
reflexivity.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].


Lemma split_array':
 forall {cs: compspecs} mid n (sh: Share.t) (t: type) 
                            v (v': list (reptype t)) v1 v2 p,
    0 <= mid <= n ->
    JMeq v v' ->
    JMeq v1 (sublist 0 mid v') ->
    JMeq v2 (sublist mid n v') ->
    Zlength v' = n ->
    sizeof (tarray t n) < Int.modulus ->
    field_compatible0 (tarray t mid) [ArraySubsc 0] p ->
    field_compatible0 (tarray t n) [ArraySubsc mid] p ->
    field_compatible0 (tarray t n) [ArraySubsc n] p ->
    data_at sh (tarray t n) v p =
    data_at sh (tarray t mid) v1  p *
    data_at sh (tarray t (n-mid)) v2 
            (field_address0 (tarray t n) [ArraySubsc mid] p).
Proof.
intros.
destruct H.
unfold data_at.
erewrite !field_at_Tarray; try reflexivity; try eassumption; try apply JMeq_refl; try reflexivity; try omega.
rewrite (split2_array_at sh _ _ 0 mid n); simpl; try omega.
autorewrite with sublist.
f_equal.
*
unfold array_at.
simpl. f_equal.
f_equal. f_equal.
admit.  
admit.
*
rewrite (array_at_data_at_rec sh _ _ mid n); auto.
change (nested_field_array_type _ _ _ _) with (tarray t (n-mid)).
rewrite (array_at_data_at_rec sh _ _ 0 (n-mid)); auto; try omega.
change (nested_field_array_type _ _ _ _) with (tarray t (n-mid-0)).
rewrite H3.
autorewrite with sublist.
f_equal.
rewrite !field_address0_clarify.
simpl. rewrite offset_offset_val. f_equal.
omega.
admit.
admit.
admit.
admit.
Admitted.

Lemma split_array:
 forall {cs: compspecs} mid n (sh: Share.t) (t: type) 
                            v (v': list (reptype t)) v1 v2 p,
    0 <= mid <= n ->
    JMeq v v' ->
    JMeq v1 (sublist 0 mid v') ->
    JMeq v2 (sublist mid n v') ->
    Zlength v' = n ->
    sizeof (tarray t n) < Int.modulus ->
    data_at sh (tarray t n) v p =
    data_at sh (tarray t mid) v1  p *
    data_at sh (tarray t (n-mid)) v2 
            (field_address0 (tarray t n) [ArraySubsc mid] p).
Proof.
intros.
apply pred_ext.
*
saturate_local.
erewrite <- split_array'; try eassumption; auto.
 +
   destruct H5 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   split3; [ | | split3; [ | | split3]]; auto.
   admit. admit. admit. split; auto. split; auto. hnf. omega.
 +
   destruct H5 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   split3; [ | | split3; [ | | split3]]; auto.
    split; auto. split; auto.
 + 
   destruct H5 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   split3; [ | | split3; [ | | split3]]; auto.
    split; auto. split; auto. hnf. omega.
*
 saturate_local.
 erewrite <- split_array'; try eassumption; auto.
 +
   destruct H5 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   split3; [ | | split3; [ | | split3]]; auto. split; auto. split; auto. hnf; omega.
 +
   destruct H5 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   destruct H8 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   split3; [ | | split3; [ | | split3]]; auto.
   admit.
   hnf in G0. rewrite field_address0_clarify in G0. 
   clear - H H4 G G0 B. destruct p; try contradiction; simpl in *.
   unfold Int.add in G0; rewrite !Int.unsigned_repr in G0.
   autorewrite with sublist in *.
   rewrite <- Z.add_assoc in G0.
   rewrite <- Z.mul_add_distr_l in G0.
   replace (mid + (n-mid)) with n in G0 by omega; auto.
   autorewrite with sublist in *.
   admit.
   autorewrite with sublist in *.
   rewrite Int.unsigned_repr.
   admit.
   admit.
   clear - B0. auto.
   split; auto.
   split; auto.
 +
   destruct H5 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   destruct H8 as [?B [?C [?D [?E [?F [?G [?J ?K]]]]]]].
   split3; [ | | split3; [ | | split3]]; auto.
   admit.
   admit.
   split; auto. split; auto. hnf;  omega.
Admitted.


Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.
change [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4] with (map Int.repr four_contents).
set (contents :=  map Vint (map Int.repr four_contents)).
assert (Zlength contents = 4) by (subst contents; reflexivity).
erewrite (split_array 2); try apply JMeq_refl; auto; try omega.
2: reflexivity.
forward_call (*  s = sumarray(four+2,2); *)
  (field_address0 (tarray tint 4) [ArraySubsc 2] four, Ews,
    sublist 2 4 four_contents,2).
+
 clear - GV. unfold gvar_denote, eval_var in *.
  destruct (Map.get (ve_of rho) _four) as [[? ?]|?]; try contradiction.
  destruct (ge_of rho _four); try contradiction. apply I.
+
 entailer!.
 unfold field_address0. rewrite if_true; auto.
 clear - H2.
  destruct H2.
  unfold field_address0 in H.
  if_tac in H; try contradiction. auto.
+
 split; auto. split. computable.
 unfold four_contents.
  unfold sublist; simpl.
  repeat constructor; computable.
+
 gather_SEP 1 2.
  replace_SEP 0 (data_at Ews (tarray tint 4) contents four).
  entailer!.
  erewrite (split_array 2 4); try apply JMeq_refl; auto; try omega.
  reflexivity.
  forward. (* return *)
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_cons body_sumarray.
semax_func_cons body_main.
Qed.

