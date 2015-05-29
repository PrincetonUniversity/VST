Require Import floyd.proofauto.
Require Import progs.revarray.

Local Open Scope logic.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list val, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed;
                writable_share sh;
                size = Zlength contents;
                forall i, 0 <= i < size -> is_int I32 Signed (zl_nth i (contents: reptype_array tint 0 size)))
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP (`(data_at sh (tarray tint size) contents a0))
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(`(data_at sh (tarray tint size) (rev contents) a0)).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_four, Tarray tint 4 noattr)::nil.

Definition Gprog : funspecs := 
    reverse_spec :: main_spec::nil.

Definition flip_between {A} lo hi (contents: list A) :=
  rev (skipn (Z.to_nat hi) contents) ++
  skipn (Z.to_nat lo) (firstn (Z.to_nat hi) contents) ++
  rev (firstn (Z.to_nat lo) contents).

Definition reverse_Inv a0 sh contents size := 
 EX j:Z,
  (PROP  (0 <= j; j <= size-j; isptr a0;
          size = Zlength contents;
          forall i, 0 <= i < size -> is_int I32 Signed (zl_nth i (contents: reptype_array tint 0 size)))
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (`(data_at sh (tarray tint size) (flip_between j (size-j) contents) a0))).

Lemma flip_fact_0: forall {A} (contents: list A),
  contents = flip_between 0 (Zlength contents - 0) contents.
Proof.
  intros.
  unfold flip_between.
  rewrite Z.sub_0_r.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite skipn_exact_length.
  change (Z.to_nat 0) with 0%nat.
  simpl.
  rewrite app_nil_r.
  rewrite firstn_exact_length.
  reflexivity.
Qed.

Lemma flip_fact_1: forall {A} (contents: list A) j,
  0 <= j ->
  Zlength contents - j - 1 <= j <= Zlength contents - j ->
  flip_between j (Zlength contents - j) contents = rev contents.
Proof.
  intros.
  assert (Zlength contents - j - 1 = j \/ Zlength contents - j = j)
    by (destruct (zle (Zlength contents - j) j); omega).
  assert (skipn (Z.to_nat j) (firstn (Z.to_nat (Zlength contents - j)) contents) = 
    rev (skipn (Z.to_nat j) (firstn (Z.to_nat (Zlength contents - j)) contents))).
  Focus 1. {
    apply len_le_1_rev.
    rewrite skipn_length.
    rewrite firstn_length.
    rewrite min_l.
    + rewrite <- Z2Nat.inj_sub by omega.
      change 1%nat with (Z.to_nat 1).
      apply Z2Nat.inj_le; omega.
    + rewrite Z2Nat.inj_sub by omega.
      rewrite Zlength_correct.
      rewrite Nat2Z.id.
      omega.
  } Unfocus.
  unfold flip_between.
  rewrite H2.
  rewrite <- !rev_app_distr.
  f_equal.
  rewrite <- firstn_firstn with (n := Z.to_nat j) (m := Z.to_nat (Zlength contents - j))
    by (apply Z2Nat.inj_le; omega).
  rewrite !firstn_skipn.
  reflexivity.
Qed.

Lemma flip_fact_2: forall {A} (contents: list A) j k d,
  0 <= j <= Zlength contents - j - 1 ->
  j <= k < Zlength contents - j ->
  Znth k (flip_between j (Zlength contents - j) contents) d = Znth k contents d.
Proof.
  intros.
  assert (Z.to_nat (Zlength contents) = length contents)
    by (rewrite Zlength_correct, Nat2Z.id; reflexivity).
  assert (Z.to_nat j <= length contents)%nat
    by (rewrite <- H1; apply Z2Nat.inj_le; omega).
  assert (Z.to_nat j <= Z.to_nat k)%nat by (apply Z2Nat.inj_le; omega).
  unfold flip_between.
  unfold Znth.
  if_tac; [omega |].
  rewrite app_nth2; rewrite rev_length, skipn_length; rewrite Z2Nat.inj_sub by omega; [| omega].
  replace (Z.to_nat k - (length contents - (Z.to_nat (Zlength contents) - Z.to_nat j)))%nat
    with (Z.to_nat k - Z.to_nat j)%nat by omega.
  rewrite app_nth1.
  Focus 2. {
    rewrite skipn_length, firstn_length.
    rewrite min_l by omega.
    rewrite <- !Z2Nat.inj_sub by omega.
    apply Z2Nat.inj_lt; omega.
  } Unfocus.
  rewrite nth_skipn.
  simpl.
  rewrite nth_firstn.
  Focus 2. {
    rewrite <- !Z2Nat.inj_sub by omega.
    rewrite <- Z2Nat.inj_add by omega.
    apply Z2Nat.inj_lt; omega.
  } Unfocus.
  f_equal.
  omega.
Qed.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function.
name a _a.
name n _n.
name lo' _lo.
name hi' _hi.
name s _s.
name t _t.

rename H2 into POP.
assert_PROP (isptr a0). entailer!.

 rename H2 into TCa0.

forward.  (* lo = 0; *)
forward _. (* hi = n; *)

forward_while (reverse_Inv a0 sh contents size)
    (PROP  () LOCAL  (temp _a a0)
   SEP (`(data_at sh (tarray tint size) (rev contents) a0)))
   j.
(* Prove that current precondition implies loop invariant *)
apply exp_right with 0.
entailer!; try omega.
f_equal; omega.
apply derives_refl'.
f_equal.
apply flip_fact_0; auto.
(* Prove that loop invariant implies typechecking condition *)
entailer!.
(* Prove that invariant && not loop-cond implies postcondition *)
entailer!.
apply derives_refl'.
f_equal.
apply flip_fact_1; omega.
(* Prove that loop body preserves invariant *)
Opaque zl_nth.
forward. (* t = a[lo]; *)
{
  entailer!.
  specialize (POP j).
  spec POP; [omega |].
  rewrite zl_nth_LZ, Z.sub_0_r in POP |- * by omega.
  rewrite flip_fact_2 by omega.
  exact POP.
}
forward.  (* s = a[hi-1]; *)
{
  entailer!.
  specialize (POP (Zlength contents - j - 1)).
  spec POP; [omega |].
  rewrite zl_nth_LZ, Z.sub_0_r in POP |- * by omega.
  rewrite flip_fact_2 by omega.
  exact POP.
}

eapply semax_seq'.
Check upd_reptype_ind.
Ltac unfold_upd_reptype t gfs v v0 := idtac.
(*
  try
  match v0 with
  | valinject ?t0 ?v0' => replace (valinject t0 v0') with v0' by reflexivity
  | _ => pose v0 as HHHHH
  end;
  rewrite (upd_reptype_ind t gfs v);
  unfold upd_reptype_rec;
  try unfold gfs;
  unfold eq_rect_r; rewrite <- !eq_rect_eq.
*)
Ltac new_store_tac := 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
  (* Super canonical field store *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let HRE := fresh "H" in
    let v0 := fresh "v" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof (nested_efield e1 efs tts))) v0 HRE;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type2 t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    let H_LEGAL := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H H_LEGAL;

    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;

    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) |-- _) =>
      match R0 with
      | appcontext [field_at] =>
        eapply (semax_SC_field_store Delta sh n) 
          with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
        [reflexivity | reflexivity | reflexivity
        | reflexivity | exact Heq | exact HLE
        | exact HRE | exact H_Denote | exact H | auto |
        | unfold_upd_reptype (nested_field_type2 t_root gfs0) gfs1 v (valinject (nested_field_type2 (nested_field_type2 t_root gfs0) gfs1) v0); reflexivity
        | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
        | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n ]
      | appcontext [field_at_] =>
        eapply (semax_SC_field_store Delta sh n)
          with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
        [reflexivity | reflexivity | reflexivity
        | reflexivity | exact Heq | exact HLE
        | exact HRE | exact H_Denote | exact H | auto 
        | unfold_upd_reptype (nested_field_type2 t_root gfs0) gfs1 v (valinject (nested_field_type2 (nested_field_type2 t_root gfs0) gfs1) v0); reflexivity
        | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
        | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n ]
      | _ =>
        eapply semax_post'; [ |
          eapply (semax_SC_field_store Delta sh n)
            with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
            [reflexivity | reflexivity | reflexivity
            | reflexivity | exact Heq | exact HLE 
            | exact HRE | exact H_Denote | exact H | auto 
            | unfold_upd_reptype (nested_field_type2 t_root gfs0) gfs1 v (valinject (nested_field_type2 (nested_field_type2 t_root gfs0) gfs1) v0) (*; reflexivity*)
            | | ]](*;
        [ match goal with
          | |- appcontext [replace_nth _ _ ?M] => 
            let EQ := fresh "EQ" in
            let MM := fresh "MM" in
               remember M as MM eqn:EQ;
               repeat match type of EQ with
                          | appcontext [field_at_ ?sh ?t nil] => change (field_at_ sh t nil) with (data_at_ sh t)
                          | appcontext [field_at ?sh ?t nil ?v] => change (field_at sh t nil v) with (data_at sh t v)
                         end;
               subst MM;
               apply derives_refl
          end
        | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
        | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
          subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n ]*)
      end
    end

  | |- @semax ?Espec ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign ?e ?e2) _ =>

 let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (mapsto_ sh (typeof e))) (eval_lvalue Delta e)) * TT) as _;
  [ unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   unfold at_offset; solve [entailer; cancel]
  |  ];
  eapply (@semax_store_nth Espec n Delta P Q R e e2);
    (unfold n,sh; clear n sh);
     [reflexivity | reflexivity |solve [entailer; cancel] | solve [auto] 
     | try solve [entailer!] ]
end.

new_store_tac.
Focus 2.

Definition eq_pose {A} x y := @eq A x y.

Definition abs_pose t (v: reptype t) : Prop := True.

Definition concr_pose t (v: reptype t) : Prop := True.

Ltac abs_or_concr t v :=
  let t' := eval compute in t in
  match t' with
  | Tarray _ _ _ =>
    match v with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: _ => assert (concr_pose t v) by exact I
    | _ => assert (abs_pose t v) by exact I
    end
  | Tstruct ?id _ =>
    let m := eval compute in (co_members (get_co id)) in
    match m with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: @nil _ => assert (concr_pose t v) by exact I
    | _ => match v with
           | (_, _) => assert (concr_pose t v) by exact I
           | _ => assert (abs_pose t v) by exact I
           end
    end
  | Tunion ?id _ =>
    let m := eval compute in (co_members (get_co id)) in
    match m with
    | @nil _ => assert (concr_pose t v) by exact I
    | _ :: @nil _ => assert (concr_pose t v) by exact I
    | _ => match v with
           | (_, _) => assert (concr_pose t v) by exact I
           | _ => assert (abs_pose t v) by exact I
           end
    end
  end.

Ltac unfold_proj_reptype_1 CS CSL t gf v HH :=
  let H := fresh "H" in
  let H1 := fresh "H" in
  let V := fresh "v" in
  let t' := eval compute in t in
  remember v as V eqn:H;
  change (@proj_gfield_reptype CS CSL t gf V) with (@proj_gfield_reptype CS CSL t' gf V) in HH;
  unfold proj_gfield_reptype in HH;
  pose proof unfold_reptype_JMeq t' V as H1;
  apply JMeq_eq in H1;
  rewrite H1 in HH; clear H1;
  subst V
(*
  match type of H0 with
  | _ = proj_struct ?i ?m V ?d =>
    let d' := eval vm_compute in d in change d with d' in H0;
    let m' := eval vm_compute in m in change m with m' in H0(*;
    cbv_proj_struct H0*)
  | _ => idtac
  end*)
.

Ltac pose_proj_reptype CS CSL t gfs v H :=
  match gfs with
  | nil =>
      assert (eq_pose (@proj_reptype CS CSL t gfs v) v) as H by reflexivity
  | ?gf :: ?gfs0 =>
     let H0 := fresh "H" in
     pose_proj_reptype CS CSL t gfs0 v H0;
     match type of H0 with
     | eq_pose (proj_reptype t gfs0 v) ?v0 => 
         match gfs0 with
         | nil => 
           assert (eq_pose
            (@proj_reptype CS CSL t gfs v)
            (proj_gfield_reptype t gf v0))
            by (unfold eq_pose in *; rewrite <- H0; unfold proj_reptype, eq_rect_r; apply eq_sym, eq_rect_eq);
           unfold_proj_reptype_1 CS CSL t gf v0 H
         | _ =>
           assert (eq_pose
            (@proj_reptype CS CSL t gfs v)
            (proj_gfield_reptype (nested_field_type2 t gfs0) gf v0))
            by (unfold eq_pose in *; rewrite <- H0; unfold proj_reptype, eq_rect_r; apply eq_sym, eq_rect_eq);
           unfold_proj_reptype_1 CS CSL (nested_field_type2 t gfs0) gf v0 H
         end
     end
  end.

Ltac pose_upd_reptype_1 CS CSL t gf v v0 H :=
  let t' := eval compute in t in
  assert (@upd_gfield_reptype CS CSL t gf v v0 = @upd_gfield_reptype CS CSL t' gf v v0) as H by reflexivity;
  unfold upd_gfield_reptype at 2 in H;
  let H0 := fresh "H" in
  pose proof unfold_reptype_JMeq t' v as H0;
  apply JMeq_eq in H0;
  rewrite H0 in H;
  clear H0;
  match type of H with
  | _ = fold_reptype ?v_res =>
    pose proof fold_reptype_JMeq t' v_res as H0;
    apply JMeq_eq in H0;
    rewrite H0 in H;
    clear H0
  end.

Ltac pose_upd_reptype CS CSL t gfs v v0 H :=
  match gfs with
  | nil => 
      assert (eq_pose (@upd_reptype_rec CS CSL t gfs v v0) v0) as H by reflexivity
  | ?gf :: ?gfs0 =>
      match goal with
      | HH : eq_pose (proj_reptype t gfs0 v) ?v1 |- _ =>
          let H_upd1 := fresh "H" in
          pose_upd_reptype_1 CS CSL (nested_field_type2 t gfs0) gf v1 v0 H_upd1;
          match type of H_upd1 with
          | _ = ?v1' =>
                  let H0 := fresh "H" in
                  pose_upd_reptype CS CSL t gfs0 v v1' H0;
                  match type of H0 with
                  | eq_pose _ ?v_res =>
                      assert (eq_pose (@upd_reptype_rec CS CSL t gfs v v0) v_res); [| clear H_upd1]
                  end
          end;
          [change (@upd_reptype_rec CS CSL t gfs v v0) with
            (@upd_reptype_rec CS CSL t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0));
           unfold eq_pose in HH; rewrite HH;
           rewrite H_upd1;
           reflexivity |]
      end
  end.

Unset Ltac Debug.

pose_proj_reptype CompSpecs CS_legal (nested_field_type2 t_root gfs0) [ArraySubsc 0] v0 H13.


pose_upd_reptype CompSpecs CS_legal (nested_field_type2 t_root gfs0) [ArraySubsc (size - j - 1)] v0 Vundef H15.

Set Printing All.

Print upd_gfield_reptype.
rewrite H16.

reflexivity.
abs_or_concr (nested_field_type2 (nested_field_type2 t_root gfs0) []) v0.

rewrite H13 in H14.







forward. (*  a[hi-1] = t ; *)
forward. (*  a[lo] = s; *)
forward lo'0. (* lo++; *)
forward hi'0. (* hi--; *)

assert (nil = upd_reptype (nested_field_type2 (tarray tint size) [])
              [ArraySubsc (size - j - 1)]
              (flip_between j (size - j) contents)
              (valinject
                 (nested_field_type2
                    (nested_field_type2 (tarray tint size) [])
                    [ArraySubsc (size - j - 1)])
                 (force_val
                    (sem_cast_neutral
                       (zl_nth j (flip_between j (size - j) contents: reptype_array tint 0 size)))))).
rewrite upd_reptype_ind.
unfold upd_reptype_rec.
unfold eq_rect_r; rewrite <- !eq_rect_eq.

unfold upd_reptype.
unfold singleton_hole; simpl singleton_hole_rec.
unfold singleton_subs. 
rewrite replace_reptype_ind.
change (nested_field_type2 (tarray tint size) []) with (tarray tint size).
unfold tarray.
cbv zeta.
rewrite (fold_reptype_JMeq (tarray tint size)).



(* Prove postcondition of loop body implies loop invariant *)
{
  apply exp_right with (Zsucc j).
  entailer.
  rewrite !flip_fact_2 by omega.
  rewrite !sem_cast_neutral_int by (exists I32, Signed; apply POP; omega).
  simpl force_val.
  entailer!. f_equal; omega.
  admit.
}
forward. (* return; *)
Qed.

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Lemma forall_Forall: forall A (P: A -> Prop) xs d,
  (forall x, In x xs -> P x) ->
  forall i, 0 <= i < Zlength xs -> P (Znth i xs d).
Proof.
  intros.
  unfold Znth.
  if_tac; [omega |].
  assert (Z.to_nat i < length xs)%nat.
  Focus 1. {
    rewrite Zlength_correct in H0.
    destruct H0 as [_ ?].
    apply Z2Nat.inj_lt in H0; [| omega | omega].
    rewrite Nat2Z.id in H0.
    exact H0.
  } Unfocus.
  forget (Z.to_nat i) as n.
  clear i H0 H1.
  revert n H2; induction xs; intros.
  + destruct n; simpl in H2; omega.
  + destruct n.
    - specialize (H a (or_introl eq_refl)).
      simpl.
      tauto.
    - simpl in *.
      apply IHxs; [| omega].
      intros.
      apply H.
      tauto.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
normalize; intro a; normalize.

forward_call'  (*  revarray(four,4); *)
  (a, Ews, map Vint four_contents, 4).
   repeat split; try computable; auto.
   intros. unfold four_contents.
   apply forall_Forall; [| auto].
   intros.
   repeat (destruct H0; [subst; simpl; auto|]); inversion H0.

forward_call'  (*  revarray(four,4); *)
    (a,Ews, rev (map Vint four_contents),4).
   repeat split; try computable; auto.
   intros. unfold four_contents.
   apply forall_Forall; [| auto].
   intros.
   repeat (destruct H0; [subst; simpl; auto|]); inversion H0.
rewrite rev_involutive.
forward. (* return s; *)
unfold main_post. entailer.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_reverse.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

