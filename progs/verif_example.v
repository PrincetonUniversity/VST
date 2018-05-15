Require Import VST.progs.conclib.
Require Import VST.progs.example.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition f_spec :=
 DECLARE _f
  WITH i : Z
  PRE [ _i OF tint ]
   PROP (repable_signed (i * i))
   LOCAL (temp _i (vint i))
   SEP ()
  POST [ tint ]
   PROP ()
   LOCAL (temp ret_temp (vint (i * i)))
   SEP ().

Definition ttask := Tstruct _task noattr.

Definition task_inv sh p := EX arg : Z, !!(repable_signed (arg * arg)) &&
  field_at sh ttask [StructField _arg] (vint arg) p *
  field_at Ews ttask [StructField _result] (vint (arg * arg)) p.

Definition g_spec :=
 DECLARE _g
  WITH p : val, x : Z * share
  PRE [ _p OF tptr tvoid ]
   let '(arg, sh) := x in
   PROP  ()
   LOCAL (temp _p p)
   SEP   ((!!(repable_signed (arg * arg) /\ readable_share sh) && emp);
          field_at sh ttask [StructField _arg] (vint arg) p;
          lock_inv sh p (task_inv sh p);
          field_at_ Ews ttask [StructField _result] p)
  POST [ tptr tvoid ]
   PROP ()
   LOCAL ()
   SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  spawn_spec; f_spec; g_spec; main_spec]).

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma inv_precise : forall sh p, precise (task_inv sh p).
Proof.
  intros; eapply derives_precise' with (Q := field_at_ _ _ _ _ * field_at_ _ _ _ _), precise_sepcon;
    auto.
  unfold task_inv; Intros r; cancel.
Qed.

Lemma inv_positive : forall sh p, positive_mpred (task_inv sh p).
Proof.
  intros; apply ex_positive.
  intro; apply positive_sepcon2.
  rewrite field_at_data_at; auto.
Qed.
Hint Resolve inv_precise inv_positive.

Lemma body_g : semax_body Vprog Gprog f_g g_spec.
Proof.
  start_function.
  forward.
  rewrite field_at_isptr; Intros.
  erewrite sem_cast_pointer2 by (try reflexivity; apply isptr_is_pointer_or_null; auto).
  forward.
  forward_call arg.
  forward.
  forward_call (p, sh, task_inv sh p).
  { lock_props.
    unfold task_inv.
    Exists arg; entailer!. }
  forward.
  (* throw away lock at the end *)
Admitted.

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_, field_at; simpl; entailer.
  unfold default_val; simpl.
  rewrite data_at_rec_eq; simpl.
  unfold struct_pred, aggregate_pred.struct_pred, at_offset, withspacer; simpl; entailer.
  (* temporarily broken *)
Admitted.

Lemma sum_base : forall l i, fold_right Z.add i l = fold_right Z.add 0 l + i.
Proof.
  induction l; auto; simpl; intro.
  rewrite IHl; omega.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name tasks _tasks.
  start_function.
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  rewrite <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z, PROP () LOCAL (gvar _tasks tasks)
    SEP (fold_right sepcon emp (map (fun j =>
           @field_at CompSpecs sh2 (tarray ttask 3) [StructField _arg; ArraySubsc j] (vint j) tasks *
           let p := force_val (sem_add_pi ttask tasks (vint j)) in
           lock_inv sh2 p (task_inv sh1 p)) (sublist 0 i (upto 3)));
         fold_right sepcon emp (map (fun j => @field_at_ CompSpecs Ews (tarray ttask 3) [ArraySubsc j] tasks) (sublist i 3 (upto 3))))).
  { entailer!.
    unfold data_at_, field_at_ at 1, field_at, at_offset; simpl; entailer!.
    rewrite data_at_rec_eq; simpl.
    unfold array_pred, aggregate_pred.array_pred; simpl.
    unfold default_val, Znth; simpl.
    unfold field_at_, field_at; simpl; entailer!. }
  { Opaque upto.
    erewrite sublist_next with (i0 := i), Znth_upto by (auto; rewrite ?Zlength_upto; simpl; omega).
    simpl.
    unfold field_at_; rewrite field_at_data_at'; Intros; simpl.
    unfold_data_at 1%nat.
    rewrite field_at_data_at'; Intros; simpl.
    forward_call (offset_val (24 * i) tasks, Ews, task_inv sh1 (offset_val (24 * i) tasks)).
    { erewrite gvar_eval_var by eauto.
      rewrite sem_add_pi_ptr; auto. }
    { rewrite (sepcon_comm _ (data_at _ _ _ _)), !sepcon_assoc; apply sepcon_derives; [|cancel].
      eapply derives_trans, lock_struct; entailer!. }
    rewrite sepcon_map, field_at_isptr; Intros.
    assert_PROP (offset_val 16 (force_val (sem_add_pi (Tstruct _task noattr) tasks (vint i))) =
      field_address ttask [StructField _arg] (offset_val (0 + 24 * i) tasks)).
    { entailer!.
      rewrite field_address_offset, offset_offset_val; auto. }
    forward.
    { entailer!.
      erewrite gvar_eval_var by eauto.
      rewrite sem_add_pi_ptr; auto. }
    get_global_function'' _g.
    apply extract_exists_pre; intros g_.
    forward_spawn (Z * share)%type (g_, offset_val (0 + 24 * i) tasks,
      fun x : Z * share => @nil (ident * val), (i, sh1),
      fun (x : Z * share) (p : val) => let '(arg, sh) := x in
        !!(repable_signed (arg * arg) /\ readable_share sh) && emp *
        field_at sh ttask [StructField _arg] (vint arg) p *
        lock_inv sh p (task_inv sh p) * field_at_ Ews ttask [StructField _result] p).
    { simpl spawn_pre; entailer!.
      { erewrite !gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ g_) by eauto.
        split; auto; split; [split; auto|].
        - rewrite sem_add_pi_ptr, force_val_sem_cast_neutral_isptr'; auto.
        - split; [transitivity (0 * 0)%Z | transitivity (3 * 3)%Z]; try computable;
            apply Z.square_le_mono_nonneg; omega. }
      Exists _p; entailer!.
      rewrite !sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'. f_equal.
        f_equal; extensionality.
        destruct x as (?, x); repeat destruct x as (x, ?); simpl.
        extensionality; apply mpred_ext; entailer!. }
      erewrite <- lock_inv_share_join; try apply Hsh; auto.
      erewrite <- field_at_share_join; try apply Hsh; auto; cancel. }
    entailer!.
    erewrite sublist_last_1, Znth_upto, map_app, sepcon_app by (rewrite ?Zlength_upto; simpl; omega).
    rewrite sepcon_map; simpl; cancel.
    rewrite sem_add_pi_ptr by auto; simpl; cancel.
    rewrite !field_at_data_at'; simpl; entailer!; auto. }
  rewrite sepcon_map; Intros; forward.
  rewrite <- seq_assoc.
  rewrite sublist_same by auto.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
    LOCAL (temp _s (vint (fold_right Z.add 0 (map (fun x => x * x)%Z (upto (Z.to_nat i))))); gvar _tasks tasks)
    SEP (fold_right sepcon emp (map (fun j =>
           @field_at CompSpecs sh2 (tarray ttask 3) [StructField _arg; ArraySubsc j] (vint j) tasks *
           let p := force_val (sem_add_pi ttask tasks (vint j)) in
           lock_inv sh2 p (task_inv sh1 p)) (upto 3));
         fold_right sepcon emp (map (fun j =>
           @field_at CompSpecs sh1 (tarray ttask 3) [StructField _arg; ArraySubsc j] (vint j) tasks *
           @field_at CompSpecs Ews (tarray ttask 3) [StructField _result; ArraySubsc j] (vint (j * j)) tasks)
           (upto (Z.to_nat i))))).
  { rewrite sepcon_map; entailer!. }
  { rewrite sepcon_map; Intros.
    erewrite extract_nth_sepcon with (i := i), Znth_map, Znth_upto by (auto; simpl; omega).
    erewrite extract_nth_sepcon with (i := i)(l := map _ (upto 3)), Znth_map, Znth_upto by (auto; simpl; omega).
    forward_call (force_val (sem_add_pi ttask tasks (vint i)), sh2,
      task_inv sh1 (force_val (sem_add_pi ttask tasks (vint i)))).
    { erewrite gvar_eval_var by eauto.
      rewrite sem_add_pi_ptr; simpl; auto. }
    unfold task_inv at 2; Intros arg.
    assert_PROP (offset_val 20 (force_val (sem_add_pi (Tstruct _task noattr) tasks (vint i))) =
      field_address ttask [StructField _result] (force_val (sem_add_pi ttask tasks (vint i)))).
    { entailer!.
      rewrite field_address_offset, offset_offset_val; auto.
      rewrite sem_add_pi_ptr in H5; auto. }
    rewrite sepcon_map; Intros; forward.
    { entailer!.
      erewrite gvar_eval_var by eauto.
      rewrite sem_add_pi_ptr; simpl; auto. }
    forward.
    assert_PROP (arg = i).
    { go_lower.
      rewrite sepcon_comm, !sepcon_assoc, <- 2sepcon_assoc; apply sepcon_derives_prop.
      rewrite (sepcon_comm (field_at _ _ _ _ _)), sepcon_assoc, sepcon_comm; apply sepcon_derives_prop.
      unfold field_at, at_offset; rewrite !data_at_rec_eq; simpl; Intros.
      rewrite sem_add_pi_ptr by auto; simpl.
      rewrite offset_offset_val.
      eapply derives_trans; [apply mapsto_value_eq; auto; discriminate|].
      apply prop_left; unfold unfold_reptype; simpl; intro; apply prop_right.
      apply repr_inj_signed; try congruence.
      - pose proof Int.min_signed_neg.
        assert (Z.abs arg <= Int.max_signed).
        { transitivity (arg * arg)%Z; [|unfold repable_signed in *; tauto].
          rewrite <- Z.abs_square.
          destruct (eq_dec (Z.abs arg) 0); [rewrite e; omega|].
          pose proof (Z.abs_nonneg arg); apply Z.le_mul_diag_r; omega. }
        destruct (Zabs_spec arg) as [[? Ha] | [? Ha]].
        { rewrite Ha in *; split; auto; omega. }
        rewrite Z.abs_le in *; split; try omega.
        unfold Int.min_signed, Int.max_signed in *; omega.
      - split; [transitivity 0 | transitivity 3]; try computable; omega. }
    subst; entailer!.
    - rewrite Z2Nat.inj_add, upto_app, map_app, fold_right_app by omega; simpl.
      change (upto 1) with [0]; simpl.
      rewrite Z2Nat.id, !Z.add_0_r by omega.
      rewrite sum_base; auto.
    - rewrite Z2Nat.inj_add, upto_app, map_app, sepcon_app by omega; simpl.
      change (upto 1) with [0]; simpl.
      rewrite Z2Nat.id, !Z.add_0_r, !sepcon_map by omega; cancel.
      erewrite extract_nth_sepcon with (i := i)(l := map _ (upto 3)), Znth_map, Znth_upto by (auto; simpl; omega).
      erewrite extract_nth_sepcon with (i := i)(l := map _ (upto 3)), Znth_map, Znth_upto by (auto; simpl; omega).
      cancel.
      rewrite sem_add_pi_ptr by auto; simpl; cancel.
      rewrite !field_at_data_at'; simpl; entailer!; auto. }
  forward.
Qed.
