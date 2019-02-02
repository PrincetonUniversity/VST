From compcert Require Export common.AST cfrontend.Ctypes cfrontend.Clight.
Export Cop.
Require Export VST.floyd.base2.
Require Export VST.floyd.functional_base.
Require Export VST.floyd.client_lemmas.
Require Export VST.floyd.go_lower.
Require Export VST.floyd.closed_lemmas.
Require Export VST.floyd.compare_lemmas.
Require Export VST.floyd.semax_tactics.
Require Export VST.floyd.forward.
Require Export VST.floyd.subsume_funspec.
Require Export VST.floyd.call_lemmas.
Require Export VST.floyd.forward_lemmas.
Require Export VST.floyd.for_lemmas.
Require Export VST.floyd.nested_pred_lemmas.
Require Export VST.floyd.nested_field_lemmas.
Require Export VST.floyd.efield_lemmas.
Require Export VST.floyd.mapsto_memory_block.
Require Export VST.floyd.aggregate_type.
Require VST.floyd.aggregate_pred. Export floyd.aggregate_pred.aggregate_pred.
Require Export VST.floyd.reptype_lemmas.
Require Export VST.floyd.simpl_reptype.
Require Export VST.floyd.data_at_rec_lemmas.
Require Export VST.floyd.field_at.
Require Export VST.floyd.field_at_wand.
Require Export VST.floyd.field_compat.
Require Export VST.floyd.stronger.
Require Export VST.floyd.loadstore_mapsto.
Require Export VST.floyd.loadstore_field_at.
Require Export VST.floyd.nested_loadstore.
Require Export VST.floyd.local2ptree_denote.
Require Export VST.floyd.local2ptree_eval.
Require Export VST.floyd.local2ptree_typecheck.
Require Export VST.floyd.proj_reptype_lemmas.
Require Export VST.floyd.replace_refill_reptype_lemmas.
Require Export VST.floyd.sc_set_load_store.
Require Export VST.floyd.unfold_data_at.
Require Export VST.floyd.entailer.
Require Export VST.floyd.globals_lemmas.
Require Export VST.floyd.diagnosis.
Require Export VST.floyd.freezer.
Require Export VST.floyd.deadvars.
Require Export VST.floyd.hints.
Require Export VST.floyd.Clightnotations.
Require VST.msl.iter_sepcon.
Require VST.msl.wand_frame.
Require VST.msl.wandQ_frame.

Arguments semax {CS} {Espec} Delta Pre%assert cmd%C Post%assert.
Export ListNotations.
Export Clight_Cop2.

Hint Rewrite add_repr mul_repr sub_repr : entailer_rewrite.
Hint Rewrite ptrofs_add_repr ptrofs_mul_repr ptrofs_sub_repr : entailer_rewrite.
Hint Rewrite mul64_repr add64_repr sub64_repr or64_repr and64_repr : entailer_rewrite.
Hint Rewrite neg_repr neg64_repr : entailer_rewrite.
Hint Rewrite ptrofs_to_int_repr: entailer_rewrite norm.

Lemma Vptrofs_unfold_false: 
Archi.ptr64 = false -> Vptrofs = fun x => Vint (Ptrofs.to_int x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma Vptrofs_unfold_true: 
Archi.ptr64 = true -> Vptrofs = fun x => Vlong (Ptrofs.to_int64 x).
Proof.
intros. unfold Vptrofs.
extensionality x.
rewrite H.
auto.
Qed.

Lemma modu_repr: forall x y, 
   0 <= x <= Int.max_unsigned ->
   0 <= y <= Int.max_unsigned ->
  Int.modu (Int.repr x) (Int.repr y) = Int.repr (x mod y).
Proof.
intros. unfold Int.modu. rewrite !Int.unsigned_repr by auto. auto.
Qed.
Hint Rewrite modu_repr using rep_omega : entailer_rewrite norm.

Hint Rewrite Vptrofs_unfold_false using reflexivity: entailer_rewrite norm.
Hint Rewrite Vptrofs_unfold_true using reflexivity: entailer_rewrite norm.

Hint Extern 1 (Vundef = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = Vundef) => reflexivity : cancel.
Hint Extern 1 (list_repeat _ Vundef = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = list_repeat _ Vundef) => reflexivity : cancel.
Hint Extern 1 (Vundef :: _ = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = Vundef :: _) => reflexivity : cancel.
Hint Extern 1 (@nil _ = default_val _) => reflexivity : cancel.
Hint Extern 1 (default_val _ = @nil _) => reflexivity : cancel.

Instance Inhabitant_mpred : Inhabitant mpred := @FF mpred Nveric.
Instance Inhabitant_share : Inhabitant share := Share.bot.

Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.
Global Transparent Archi.ptr64.

Ltac step :=
  first
  [ progress Intros
  | progress autorewrite with sublist in * |-
  | progress autorewrite with sublist
  | progress autorewrite with norm
  | let x := fresh "x" in
    Intros x
  | forward
  | forward_if
  | forward_call
  | rep_omega
  | cstring'
  | list_solve
  | EExists
  | cstring1
  | deadvars!
  | progress_entailer
  | match goal with |- _ /\ _ => split end
  ].

Ltac info_step :=
  first
  [ progress Intros; idtac "Intros."
  | progress autorewrite with sublist in * |-; idtac "autorewrite with sublist in * |-."
  | progress autorewrite with sublist; idtac "autorewrite with sublist."
  | progress autorewrite with norm; idtac "autorewrite with norm."
  | let x := fresh "x" in
    Intros x;
    idtac "Intros x."
  | forward; idtac "forward."
  | forward_if; idtac "forward_if."
  | forward_call; idtac "forward_call."
  | rep_omega; idtac "rep_omega."
  | cstring'; idtac "cstring'."
  | list_solve; idtac "list_solve."
  | EExists; idtac "EExists."
  | cstring1; idtac "cstring1."
  | deadvars!; idtac "deadvars!."
  | progress_entailer; idtac "progress_entailer."
  | match goal with |- _ /\ _ => split end; idtac "split."
  ].



(* solve list equations *)
(* interpreted functions :
  Zlength
  app
  list_repeat / Zlist_repeat
  map
  sublist
  upd_Znth -> sublist
  Znth -> sublist
*)

Definition Zlist_repeat {A : Type} (n : Z) (x : A) : list A :=
  list_repeat (Z.to_nat n) x.

Lemma Zlength_Zlist_repeat : forall (A : Type) (n : Z) (x : A),
  0 <= n ->
  Zlength (Zlist_repeat n x) = n.
Proof. apply @Zlength_list_repeat. Qed.

Ltac Zlength_solve := autorewrite with Zlength; pose_Zlength_nonneg; omega.
Hint Rewrite Zlength_nil : Zlength.
Hint Rewrite Zlength_app : Zlength.
Hint Rewrite Zlength_map : Zlength.
Hint Rewrite Zlength_Zlist_repeat using Zlength_solve : Zlength.
Hint Rewrite @Zlength_list_repeat using Zlength_solve : Zlength.
Hint Rewrite @upd_Znth_Zlength using Zlength_solve : Zlength.
Hint Rewrite @Zlength_sublist using Zlength_solve : Zlength.

Lemma Zlist_repeat_fold : forall (A : Type) (n : Z) (x : A),
  list_repeat (Z.to_nat n) x = Zlist_repeat n x.
Proof. auto. Qed.

Lemma cons_Zlist_repeat_1_app : forall (A : Type) (x : A) (al : list A),
  x :: al = Zlist_repeat 1 x ++ al.
Proof. auto. Qed.

Lemma upd_Znth_unfold : forall (A : Type) (n : Z) (al : list A) (x : A),
  upd_Znth n al x = sublist 0 n al ++ [x] ++ sublist (n+1) (Zlength al) al.
Proof. auto. Qed.

Lemma Znth_singleton_sublist : forall (A : Type) (d : Inhabitant A) (i : Z) (al : list A),
  0 <= i < Zlength al ->
  [Znth i al] = sublist i (i+1) al.
Proof. intros. rewrite sublist_one by omega; auto. Qed.

Lemma Znth_Zlist_repeat_1_sublist : forall (A : Type) (d : Inhabitant A) (i : Z) (al : list A),
  0 <= i < Zlength al ->
  Zlist_repeat 1 (Znth i al) = sublist i (i+1) al.
Proof. intros. rewrite sublist_one by omega; auto. Qed.

Hint Rewrite Zlist_repeat_fold upd_Znth_unfold Znth_singleton_sublist cons_Zlist_repeat_1_app : list_form.
Hint Rewrite Znth_Zlist_repeat_1_sublist using Zlength_solve: list_form.
Hint Rewrite <- Znth_map using Zlength_solve: list_form.

Lemma Znth_map2 : forall (B : Type) (db : Inhabitant B) (A : Type) (da : Inhabitant A) (i : Z) (f : A -> B) (al : list A),
  0 <= i < Zlength al ->
  Znth i (map f al) = f (Znth i al).
Proof. intros. apply Znth_map; auto. Qed.

Hint Rewrite <- (@Znth_map2 float32 Inhabitant_float32) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 ptrofs Inhabitant_ptrofs) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 int64 Inhabitant_int64) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 byte Inhabitant_byte) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 int Inhabitant_int) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 val Inhabitant_val) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 Z Inhabitant_Z) using Zlength_solve : list_form.
Hint Rewrite <- (@Znth_map2 nat Inhabitant_nat) using Zlength_solve : list_form.

Ltac list_form :=
  autorewrite with list_form.

Lemma Znth_Zlist_repeat : forall (A : Type) (d : Inhabitant A) (i n : Z) (x : A),
  0 <= i < n ->
  Znth i (Zlist_repeat n x) = x.
Proof. intros. apply Znth_list_repeat_inrange; auto. Qed.

Lemma sublist_Zlist_repeat : forall (A : Type) (lo hi n : Z) (x : A),
  0 <= lo <= hi -> hi <= n ->
  sublist lo hi (Zlist_repeat n x) = Zlist_repeat (hi - lo) x.
Proof. intros. apply sublist_list_repeat; omega. Qed.

Lemma map_Zlist_repeat : forall (A B : Type) (f : A -> B) (n : Z) (x : A),
  map f (Zlist_repeat n x) = Zlist_repeat n (f x).
Proof. intros. apply map_list_repeat. Qed.

Hint Rewrite sublist_Zlist_repeat Znth_Zlist_repeat using Zlength_solve : sublist2.
Hint Rewrite map_Zlist_repeat @map_sublist map_app : sublist2.
Hint Rewrite sublist_app1 @sublist_app2 @sublist_app' using Zlength_solve : sublist2.
Hint Rewrite app_nil_l app_nil_r : sublist2.
Hint Rewrite <- app_assoc : sublist2.

Ltac list_normalize :=
  list_form; autorewrite with sublist2.

Lemma list_split : forall (A : Type) (i : Z) (l : list A),
  0 <= i <= Zlength l ->
  l = sublist 0 i l ++ sublist i (Zlength l) l.
Proof.
  intros. rewrite <- sublist_same at 1 by auto. apply sublist_split; omega.
Qed.

Ltac list_deduce :=
  lazymatch goal with
  | |- @eq (list _) _ _ => idtac
  | |- _ => fail "list_deduce can only solve list equations"
  end;
  let A :=
    match goal with |- @eq (list ?A) _ _ => A end
  in
  lazymatch goal with
  | |- (?l1 ++ ?l2) = ?r => idtac
  | |- ?l = ?r =>
    rewrite <- (app_nil_r l) at 1
  end;
  lazymatch goal with
  | |- ?l = (?r1 ++ ?r2) => idtac
  | |- ?l = ?r =>
    symmetry; rewrite <- (app_nil_r r) at 1; symmetry
  end;
  let ltail := fresh in
  let rtail := fresh in
  lazymatch goal with
  | |- (?l1 ++ ?l2) = (?r1 ++ ?r2) =>
    pose (ltail := l2); pose (rtail := r2);
    change (l1 ++ ltail = r1 ++ rtail);
    let H := fresh in
    first
    [ assert (H : Zlength l1 = Zlength r1) by Zlength_solve
    | assert (H : Zlength l1 <= Zlength r1) by Zlength_solve;
      let left := fresh in
      pose (left := l1);
      change (left ++ ltail = r1 ++ rtail);
      rewrite (list_split A (Zlength l1) r1) by Zlength_solve;
      rewrite <- app_assoc;
      subst left
    | assert (H : Zlength l1 >= Zlength r1) by Zlength_solve;
      let right := fresh in
      pose (right := l1);
      change (l1 ++ ltail = right ++ rtail);
      rewrite (list_split A (Zlength r1) l1) by Zlength_solve;
      rewrite <- app_assoc;
      subst right
    ];
    clear H;
    subst ltail rtail;
    f_equal
  end;
  list_normalize.

Hint Rewrite @sublist_sublist using Zlength_solve : sublist2.







(* solve list equation by list extentionality *)
Lemma nth_eq_ext : forall (A : Type) (default : A) (al bl : list A),
  length al = length bl ->
  (forall (i : nat), (0 <= i < length al)%nat -> nth i al default = nth i bl default) ->
  al = bl.
Proof.
  intros. generalize dependent bl.
  induction al; intros;
    destruct bl; try discriminate; auto.
  f_equal.
  - apply (H0 0%nat). simpl. omega.
  - apply IHal.
    + simpl in H. omega.
    + intros. apply (H0 (S i)). simpl. omega.
Qed.

Lemma Znth_eq_ext : forall (A : Type) (d : Inhabitant A) (al bl : list A),
  Zlength al = Zlength bl ->
  (forall (i : Z), 0 <= i < Zlength al -> Znth i al = Znth i bl) ->
  al = bl.
Proof.
  intros. rewrite !Zlength_correct in *. apply nth_eq_ext with d.
  - omega.
  - intros. rewrite  <- (Nat2Z.id i).
    specialize (H0 (Z.of_nat i) ltac:(omega)).
    rewrite !nth_Znth by (rewrite !Zlength_correct in *; omega).
    apply H0.
Qed.

Hint Resolve Znth_eq_ext : list_ext.

Hint Rewrite @Znth_list_repeat_inrange using Zlength_solve : Znth_solve.
Hint Rewrite @Znth_sublist using Zlength_solve : Znth_solve.
Hint Rewrite app_Znth1 app_Znth2 using Zlength_solve : Znth_solve.
Hint Rewrite Znth_Zlist_repeat using Zlength_solve : Znth_solve.

Hint Rewrite (@Znth_map _ Inhabitant_float32) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_ptrofs) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_int64) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_byte) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_int) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_val) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_Z) using Zlength_solve : Znth_solve.
Hint Rewrite (@Znth_map _ Inhabitant_nat) using Zlength_solve : Znth_solve.

Ltac Znth_solve :=
  autorewrite with Znth_solve;
  autorewrite with Zlength;
  auto;
  try match goal with
  | |- context [Znth ?n (app ?al ?bl)] =>
    let H := fresh in
    pose (H := Z_lt_le_dec n (Zlength al));
    autorewrite with Zlength in H; destruct H;
    Znth_solve
  end.

