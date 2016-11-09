Require Import floyd.proofauto.
Require Import progs.load_demo.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition pair_pair_t := (Tstruct _pair_pair noattr).

Definition array_size := 100.

Definition get22_spec :=
 DECLARE _get22
  WITH pps: val, i: Z, x11: int, x12: int, x21: int, x22: int, sh : share
  PRE [ _pps OF (tptr pair_pair_t), _i OF tint ]
    PROP  (readable_share sh; 0 <= i < array_size)
    LOCAL (temp _pps pps; temp _i (Vint (Int.repr i)))
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i] 
                    ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps)
  POST [ tint ]
        PROP () LOCAL (temp ret_temp (Vint x22))
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                    ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [get22_spec; main_spec].

(* Simplified Hoare triple proven by this lemma:
  {e is an lvalue pointing to p.gfs, and at p.gfs, the value v is stored}
  id = e
  {the local variable id stores the value v}
*)
Lemma semax_max_path_field_load_nth_ram':
  forall {Espec: OracleKind},
    forall n Delta sh id P Q R (e: expr) Pre
      (t t_root: type) (gfs: list gfield)
      (p v : val) (v' : reptype (nested_field_type t_root gfs)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      typeof e = nested_field_type t_root gfs ->
      readable_share sh ->
      type_is_volatile (typeof e) = false ->
      JMeq v' v ->
      nth_error R n = Some Pre ->
      Pre |-- field_at sh t_root gfs v' p * TT ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root (* was t before *) gfs p)) (eval_lvalue e)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H0.
  rewrite H1 in H8.
  assert_PROP (field_compatible t_root gfs p). {
    erewrite SEP_nth_isolate, <- insert_SEP by eauto.
    apply andp_left2;
    apply derives_left_sepcon_right_corable; auto.
    intro rho; unfold_lift; simpl.
    eapply derives_trans; [apply H6 |].
    rewrite field_at_compatible'.
    normalize.
  }
  eapply semax_load_nth_ram; try eassumption.
  + eapply self_ramify_trans; [exact H6 |].
    eapply RAMIF_PLAIN.weak_ramif_spec.
    apply mapsto_field_at_ramify; try rewrite <- H1; eauto.
Qed.

(* Simplified Hoare triple proven by this lemma:
  {e is an lvalue pointing to p.gfs0.gfs1
   at p.gfs0, the value v' is stored
   v'.gfs1 = v}
  id = e
  {the local variable id stores the value v}
*)
Lemma semax_SC_field_load':
  forall {Espec: OracleKind},
    forall Delta sh n id P Q R (e: expr)
      (t t_root: type) (gfs0 gfs1 gfs: list gfield)
      (p: val) (v : val) (v' : reptype (nested_field_type t_root gfs0)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof e) t = true ->
      type_is_volatile (typeof e) = false ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfs p)) (eval_lvalue e)) ->
      typeof e = nested_field_type t_root gfs ->
      gfs = gfs1 ++ gfs0 ->
      nth_error R n = Some (field_at sh t_root gfs0 v' p) ->
      readable_share sh ->
      JMeq (proj_reptype (nested_field_type t_root gfs0) gfs1 v') v ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e) &&
        local `(tc_val (typeof e) v) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (!! legal_nested_field t_root gfs) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e)
          (normal_ret_assert
            (PROPx P 
              (LOCALx (temp id v :: remove_localdef id Q)
                (SEPx R)))).
Proof.
  intros.
  eapply semax_extract_later_prop'; [exact H9 | clear H9; intro H9].
  assert (JMeq (valinject (nested_field_type t_root gfs) v) v) as A. {
    apply valinject_JMeq. apply is_neutral_cast_by_value with t. rewrite <- H3. assumption.
  }
  eapply semax_max_path_field_load_nth_ram'.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  exact A.
  eassumption.
  2: eassumption.
  2: eassumption.
  eapply derives_trans; [apply nested_field_ramif' with (gfs3 := gfs1) |].
  + eapply JMeq_trans; [apply H7 |].
    rewrite H4 in A.
    apply @JMeq_sym, A.
  + rewrite <- H4; auto.
  + apply sepcon_derives; [| auto].
    rewrite <- H4.
    apply derives_refl.
Qed.

Inductive undo_and_first__assert_PROP: Prop -> Prop := .

Require Import floyd.simpl_reptype.

(* Given gfs and gfs0, pose gfs1 such that (gfs = gfs1 ++ gfs0) *)
Ltac find_prefix gfs gfs0 gfs1 :=
  let len := fresh "len" in
  pose ((length gfs - length gfs0)%nat) as len;
  simpl in len;
  match goal with
  | len := ?len' |- _ => pose (gfs1 := (firstn len' gfs)); cbv [gfs firstn] in gfs1
  end;
  unify gfs (gfs1 ++ gfs0).

Ltac find_SEP_clause_for p Rs i t_root gfs (*<-input  output->*) gfs0 gfs1 v n := 
match Rs with
| ?R :: ?Rest => match R with
  | field_at ?SH ?T ?GFS0 ?V ?P =>
      unify T t_root; unify P p;
      find_prefix gfs GFS0 gfs1;
      instantiate (gfs0 := GFS0);
      instantiate (v := V); pose (n := i); cbv in n
(* todo update
  | data_at ?SH ?T ?V p =>
      pose (nT := T); pose (nGfs := (@nil gfield));
      pose (nV := V); pose (nn := i); cbv in nn
  | field_at_ ?SH ?T ?gfs p =>
      pose (nT := T); pose (nGfs := gfs);
      pose (nV := (default_val (nested_field_type T gfs))); pose (nn := i); cbv in nn
  | data_at_ ?SH ?T p =>
      pose (nT := T); pose (nGfs := (@nil gfield));
      pose (nV := (default_val (nested_field_type T []))); pose (nn := i); cbv in nn
*)
  | _ => find_SEP_clause_for p Rest (S i) t_root gfs gfs0 gfs1 v n
  end
end.

Ltac solve_legal_nested_field_in_entailment ::=
   match goal with
   | |- _ |-- !! legal_nested_field ?t_root ?gfs =>
     try unfold t_root;
     try unfold gfs;
     try match gfs with
     | (?gfs1 ++ ?gfs0) => try unfold gfs1; try unfold gfs0
     end
  end;
  first
  [ apply prop_right; apply compute_legal_nested_field_spec';
    match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor; omega
  |
  apply compute_legal_nested_field_spec;
  match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor;
  try solve [apply prop_right; auto; omega];
  try solve [normalize; apply prop_right; auto; omega]
  ].

Ltac construct_nested_efield_no_change e e1 efs tts :=
  let pp := fresh "pp" in
    pose (compute_nested_efield e) as pp;
    simpl in pp;
    pose (fst (fst pp)) as e1;
    pose (snd (fst pp)) as efs;
    pose (snd pp) as tts;
    simpl in e1, efs, tts;
    unify e (nested_efield e1 efs tts); (* just a sanity check *)
    clear pp.

Ltac load_tac ::=
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with   
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ (Ecast ?e _)) _ =>
 (* Super canonical cast load *)
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

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H;
    
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
    | (ENTAIL _, PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;
    eapply (semax_SC_field_cast_load Delta sh n) with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    [ reflexivity
    | reflexivity
    | now (clear; let H := fresh in intro H; inversion H)
    | solve [subst sh; auto] (* readable share *)
    | reflexivity
    | reflexivity
    | reflexivity
    | reflexivity
    | exact Heq
    | exact HLE
    | exact H_Denote
    | solve_load_rule_evaluation
    | clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n;
      repeat match goal with H := _ |- _ => clear H end;
      try quick_typecheck3; 
      unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
      try solve [entailer!]
    | solve_legal_nested_field_in_entailment;
      try clear Heq HLE H_Denote H;
      subst e1 gfs0 gfs1 efs tts t_root v sh lr n
    ]

| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
 (* Super canonical load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield_no_change e e1 efs tts;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
    do_compute_lvalue Delta P Q R e p HLE; (* note: we compute lvalue of whole e, not just e1 *)

    let H_Denote := fresh "H" in
    let gfsB := fresh "gfsB" in
      solve_efield_denote Delta P Q R efs gfsB H_Denote;

    (* If a is the "base pointer" of the SEP clause to be used,
    the path to the value can be split in 2 ways:
    - a.gfsA.gfsB :  a.gfsA corresponds to e1, and gfsB corresponds to efs
    - a.gfs0.gfs1 :  a.gfs0 is what we have a SEP clause for, and gfs1 goes from there to final value *)

    let t_root := fresh "t_root" in evar (t_root: type);
    let gfsA := fresh "gfsA" in evar (gfsA: list gfield);
    let a := fresh "a" in evar (a: val);
    let eq := constr:(p = field_address t_root (gfsB ++ gfsA) a) in
    (*let g := constr:(ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! eq) in*)
    let Eq := fresh "Eqname" in
    tryif
      assert eq as Eq by (first
        [ subst p gfsA gfsB a t_root; eassumption
        | instantiate (gfsA := []); rewrite app_nil_r; reflexivity ])
    then (

    rewrite Eq in *; clear Eq p;
    let gfsAll := fresh "gfsAll" in pose (gfsAll := (gfsB ++ gfsA));
    cbv [gfsA gfsB app] in gfsAll;
    let gfs0 := fresh "gfs0" in evar (gfs0: list gfield);
    let gfs1 := fresh "gfs1" in
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    find_SEP_clause_for a R O t_root gfsAll gfs0 gfs1 v n;

    eapply semax_SC_field_load' with (n0 := n) (t_root0 := t_root) 
      (gfs2 := gfs0) (gfs3 := gfs1) (gfs := gfsAll) (p := a);
    [ reflexivity
    | reflexivity
    | reflexivity
    | exact HLE
    | reflexivity
    | reflexivity
    | try unfold data_at; try unfold data_at_; try unfold field_at_; subst n;
      cbv [nth_error]; reflexivity
    | auto (* readable_share *)
    | solve_load_rule_evaluation
    | clear HLE H_Denote;
      subst e1 gfs0 gfs1 gfsA gfsB gfsAll efs tts t_root a v n;
      repeat match goal with H := _ |- _ => clear H end;
      try quick_typecheck3; 
      unfold tc_efield, tc_LR, tc_LR_strong; simpl typeof;
      try solve [entailer!]
    | solve_legal_nested_field_in_entailment; try clear HLE H_Denote;
      subst e1 gfs0 gfs1 gfsA gfsB gfsAll efs tts t_root a v n]

    ) else assert (undo_and_first__assert_PROP eq); subst t_root gfsA gfsB a p
end.


Lemma body_go: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.
(* int res = p->snd; *)

assert_PROP (isptr pps) as Ip by entailer!.

(* Hint given by forward: *)
assert_PROP (offset_val 4
     (offset_val 8 (force_val (sem_add_pi (Tstruct _pair_pair noattr) pps (Vint (Int.repr i))))) =
   field_address (tarray pair_pair_t array_size) ([StructField _snd] ++ [StructField _right; ArraySubsc i]) pps). {
  entailer!.
  rewrite field_compatible_field_address.
  destruct pps; inversion Ip. simpl. do 3 f_equal. omega.
  auto with field_compatible.
}

forward.

forward.
Qed.
