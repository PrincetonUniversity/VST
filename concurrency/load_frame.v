Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import compcert.ia32.Op.
Require Import compcert.backend.Locations.
Require Import compcert.backend.Conventions.
Require compcert.ia32.Stacklayout.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.val_casted.
Require Import ccc26x86.BuiltinEffects.
Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.effect_properties.
Require Import VST.sepcomp.reach.
Require Import msl.Axioms.

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: int) :=
  Mem.loadv (chunk_of_type ty) m (Val.add sp (Vint ofs)).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: int) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.add sp (Vint ofs)) v.

(*NOTE [store_args_simple] is used to model program loading of
  initial arguments.  Cf. NOTE [loader] below. *)

Fixpoint store_args0 (m: mem) (sp: val) (ofs: Z) (args: list val) (tys: list typ)
         : option mem :=
  match args,tys with
    | nil,nil => Some m
    | a::args',ty::tys' =>
      match store_stack m sp ty (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) a with
        | None => None
        | Some m' => store_args0 m' sp (ofs+typesize ty) args' tys'
      end
    | _,_ => None
  end.

(* [store_args_rec] is more complicated, but more precise than,
   [store_args (encode_longs args) (encode_typs tys)]. Still, it's not totally
   satisfactory that argument encoding code is duplicated like this. *)

Fixpoint store_args_rec m sp ofs args tys : option mem :=
  let vsp := Vptr sp Int.zero in
  match tys, args with
    | nil, nil => Some m
    | ty'::tys',a'::args' =>
      match ty', a' with
        | Tlong, Vlong n =>
          match store_stack m vsp Tint (Int.repr (Stacklayout.fe_ofs_arg + 4*(ofs+1)))
                            (Vint (Int64.hiword n)) with
            | None => None
            | Some m' =>
              match store_stack m' vsp Tint (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs))
                                (Vint (Int64.loword n)) with
                | None => None
                | Some m'' => store_args_rec m'' sp (ofs+2) args' tys'
              end
          end
        | Tlong, _ => None
        | _,_ =>
          match store_stack m vsp ty' (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) a' with
            | None => None
            | Some m' => store_args_rec m' sp (ofs+typesize ty') args' tys'
          end
      end
    | _, _ => None
  end.

Lemma store_stack_fwd m sp t i a m' :
  store_stack m sp t i a = Some m' ->
  mem_forward m m'.
Proof.
unfold store_stack, Mem.storev.
destruct (Val.add sp (Vint i)); try solve[inversion 1].
apply store_forward.
Qed.

Lemma store_args_fwd sp ofs args tys m m' :
  store_args_rec m sp ofs args tys = Some m' ->
  mem_forward m m'.
Proof.
revert args ofs m; induction tys.
simpl. destruct args. intros ofs. inversion 1; subst.
solve[apply mem_forward_refl].
intros ofs m. simpl. inversion 1.
destruct args; try solve[inversion 1].
destruct a; simpl; intros ofs m.
- case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.
- case_eq (store_stack m (Vptr sp Int.zero) Tfloat
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.
- destruct v; try solve[congruence].
case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                      | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.hiword i))).
intros m0 EQ. apply store_stack_fwd in EQ.
case_eq (store_stack m0 (Vptr sp Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.loword i))). intros m1 H H2.
eapply mem_forward_trans; eauto.
eapply mem_forward_trans; eauto.
eapply store_stack_fwd; eauto. intros; congruence. intros; congruence.
- case_eq (store_stack m (Vptr sp Int.zero) Tsingle
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.
- case_eq (store_stack m (Vptr sp Int.zero) Tany32
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.
- case_eq (store_stack m (Vptr sp Int.zero) Tany64
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.

Qed.

Lemma store_stack_unch_on stk z t i a m m' :
  store_stack m (Vptr stk z) t i a = Some m' ->
  Mem.unchanged_on (fun b ofs => b<>stk) m m'.
Proof.
unfold store_stack, Mem.storev.
case_eq (Val.add (Vptr stk z) (Vint i)); try solve[inversion 1].
intros b i0 H H2. eapply Mem.store_unchanged_on in H2; eauto.
intros i2 H3 H4. inv H. apply H4; auto.
Qed.

Lemma store_args_unch_on stk ofs args tys m m' :
  store_args_rec m stk ofs args tys = Some m' ->
  Mem.unchanged_on (fun b ofs => b<>stk) m m'.
Proof.
revert args ofs m; induction tys.
simpl. destruct args. intros ofs. inversion 1; subst.
  solve[apply Mem.unchanged_on_refl].
intros ofs m. simpl. inversion 1.
destruct args; try solve[inversion 1].
destruct a; simpl; intros ofs m.
- case_eq (store_stack m (Vptr stk Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto.
solve[eapply store_stack_fwd; eauto]. intros; congruence.
- case_eq (store_stack m (Vptr stk Int.zero) Tfloat
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto.
solve[eapply store_stack_fwd; eauto]. intros; congruence.
- destruct v; try solve[inversion 1].
case_eq (store_stack m (Vptr stk Int.zero) Tint
           (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                      | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.hiword i))).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ.
case_eq (store_stack m0 (Vptr stk Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.loword i))).
intros m1 EQ2. generalize EQ2 as EQ2'. intro. apply store_stack_unch_on in EQ2. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto.
eapply unchanged_on_trans with (m2 := m1); eauto.
eapply store_stack_fwd; eauto. eapply store_stack_fwd; eauto.
intros; congruence. intros; congruence.
- case_eq (store_stack m (Vptr stk Int.zero) Tsingle
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto.
solve[eapply store_stack_fwd; eauto]. intros; congruence.
- case_eq (store_stack m (Vptr stk Int.zero) Tany32
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto.
solve[eapply store_stack_fwd; eauto]. intros; congruence.
- case_eq (store_stack m (Vptr stk Int.zero) Tany64
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto.
solve[eapply store_stack_fwd; eauto]. intros; congruence.
Qed.

Fixpoint args_len_rec args tys : option Z :=
  match tys, args with
    | nil, nil => Some 0
    | ty'::tys',a'::args' =>
      match ty', a' with
        | Tlong, Vlong n =>
          match args_len_rec args' tys' with
            | None => None
            | Some z => Some (2+z)
          end
        | Tlong, _ => None
        | Tfloat,_ =>
          match args_len_rec args' tys' with
            | None => None
            | Some z => Some (2+z)
          end
        | _,_ =>
          match args_len_rec args' tys' with
            | None => None
            | Some z => Some (1+z)
          end
      end
    | _, _ => None
  end.

Lemma args_len_rec_succeeds args tys
      (VALSDEF: val_casted.vals_defined args=true)
      (HASTY: Val.has_type_list args tys) :
  exists z, args_len_rec args tys = Some z.
Proof.
rewrite val_casted.val_has_type_list_func_charact in HASTY.
revert args VALSDEF HASTY; induction tys. destruct args; auto.
simpl. exists 0; auto. simpl. intros; congruence.
destruct args. simpl. intros; congruence.
unfold val_has_type_list_func; rewrite andb_true_iff. intros VD [H H2].
fold val_has_type_list_func in H2.
apply IHtys in H2. destruct H2 as [z H2]. simpl.
destruct a; try solve [rewrite H2; eexists; eauto].
destruct v; simpl in H; try solve [simpl in VD; congruence].
rewrite H2. eexists; eauto.
simpl in VD. destruct v; auto. congruence.
Qed.

Lemma range_perm_shift m b lo sz n k p :
  0 <= lo -> 0 <= sz -> 0 <= n ->
  Mem.range_perm m b lo (lo+sz+n) k p ->
  Mem.range_perm m b (lo+n) (lo+sz+n) k p.
Proof. intros A B C RNG ofs [H H2]; apply RNG; omega. Qed.

Inductive only_stores (sp: block) : list val -> mem -> mem -> Type :=
| only_stores_nil m : only_stores sp nil m m
| only_stores_cons m ch ofs v m'' m' l :
    Mem.store ch m sp ofs v = Some m'' ->
    only_stores sp l m'' m' ->
    only_stores sp (v::l) m m'.

Lemma only_stores_fwd sp m m' l :
  only_stores sp l m m' -> mem_forward m m'.
Proof.
induction 1. apply mem_forward_refl.
eapply mem_forward_trans. eapply store_forward; eauto. apply IHX.
Qed.

Lemma store_args_rec_only_stores m sp args tys z m' :
  store_args_rec m sp z args tys = Some m' ->
  only_stores sp (encode_longs tys args) m m'.
Proof.
revert args z m. induction tys. destruct args; simpl.
intros ? ?; inversion 1. constructor.
intros ? ? ?; congruence.
destruct args; simpl. intros; congruence. intros z m.
generalize
 (Int.repr match z with
             | 0 => 0 | Z.pos y' => Z.pos y'~0~0
             | Z.neg y' => Z.neg y'~0~0 end) as z'.
generalize
 (Int.repr match z+1 with
             | 0 => 0 | Z.pos y' => Z.pos y'~0~0
             | Z.neg y' => Z.neg y'~0~0 end) as z''.
intros z'' z'. destruct a.
- case_eq (store_stack m (Vptr sp Int.zero) Tint z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H.
solve[eapply only_stores_cons; eauto].
- case_eq (store_stack m (Vptr sp Int.zero) Tfloat z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H.
solve[eapply only_stores_cons; eauto].
- destruct v; try solve[intros; congruence].
case_eq (store_stack m (Vptr sp Int.zero) Tint z'' (Vint (Int64.hiword i)));
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE.
case_eq (Mem.store Mint32 m0 sp (Int.unsigned (Int.add Int.zero z'))
                   (Vint (Int64.loword i)));
  try solve[intros; congruence].
intros m1 STORE' H.
eapply only_stores_cons; eauto.
solve[eapply only_stores_cons; eauto].
- case_eq (store_stack m (Vptr sp Int.zero) Tsingle z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H.
solve[eapply only_stores_cons; eauto].
- case_eq (store_stack m (Vptr sp Int.zero) Tany32 z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H.
solve[eapply only_stores_cons; eauto].
- case_eq (store_stack m (Vptr sp Int.zero) Tany64 z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H.
solve[eapply only_stores_cons; eauto].
Qed.

Lemma args_len_recD: forall v args tp tys sz,
     args_len_rec (v :: args) (tp :: tys) = Some sz ->
     exists z1 z2, sz = z1+z2 /\ args_len_rec args tys = Some z2 /\
        match tp with Tlong => z1=2 | Tfloat => z1=2 | _ => z1=1 end.
Proof.
simpl. intros.
destruct tp; simpl in *.
destruct (args_len_rec args tys); inv H.
  exists 1, z; repeat split; trivial.
destruct (args_len_rec args tys); inv H.
  exists 2, z; repeat split; trivial.
destruct v; inv H.
  destruct (args_len_rec args tys); inv H1.
  exists 2, z; repeat split; trivial.
destruct (args_len_rec args tys); inv H.
  exists 1, z; repeat split; trivial.
destruct (args_len_rec args tys); inv H.
  exists 1, z; repeat split; trivial.
destruct (args_len_rec args tys); inv H.
  exists 1, z; repeat split; trivial.
Qed.

Lemma args_len_rec_nonneg: forall tys args sz,
     args_len_rec args tys = Some sz -> 0 <= sz.
Proof.
intros tys; induction tys; intros.
  destruct args; inv H. omega.
destruct args; inv H.
  destruct a; specialize (IHtys args).
+ destruct (args_len_rec args tys); inv H1.
    specialize (IHtys _ (eq_refl _)).
    destruct z. omega. destruct p; xomega.
    xomega.
+ destruct (args_len_rec args tys); inv H1.
    specialize (IHtys _ (eq_refl _)).
    destruct z. omega. destruct p; xomega.
    xomega.
+ destruct v; inv H1.
    destruct (args_len_rec args tys); inv H0.
    specialize (IHtys _ (eq_refl _)).
    destruct z. omega. destruct p; xomega.
    xomega.
+ destruct (args_len_rec args tys); inv H1.
    specialize (IHtys _ (eq_refl _)).
    destruct z. omega. destruct p; xomega.
    xomega.
+ destruct (args_len_rec args tys); inv H1.
    specialize (IHtys _ (eq_refl _)).
    destruct z. omega. destruct p; xomega.
    xomega.
+ destruct (args_len_rec args tys); inv H1.
    specialize (IHtys _ (eq_refl _)).
    destruct z. omega. destruct p; xomega.
    xomega.
Qed.

Lemma args_len_rec_pos: forall v args tp tys sz,
     args_len_rec (v :: args) (tp :: tys) = Some sz -> 0 < sz.
Proof. intros.
apply args_len_recD in H. destruct H as [? [? [? [? ?]]]]; subst.
apply args_len_rec_nonneg in H0.
destruct tp; omega.
Qed.

Definition store_arg m sp ofs ty' a' :=
      match ty', a' with
        | Tlong, Vlong n =>
          match store_stack m (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(ofs+1)))
                            (Vint (Int64.hiword n)) with
            | None => None
            | Some m' =>
                match  store_stack m' (Vptr sp Int.zero) Tint
                      (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs))
                                (Vint (Int64.loword n)) with
                | None => None
                | Some m'' => Some (m'',ofs+2)
                end
          end
        | Tlong, _ => None
        | _,_ =>
          match store_stack m (Vptr sp Int.zero) ty'
                 (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) a' with
            | None => None
            | Some m' => Some (m', ofs+typesize ty')
          end
      end.

Lemma store_argSZ m sp z ty v m' ofs:
      store_arg m sp z ty v = Some(m',ofs) -> ofs = z + typesize ty.
Proof. destruct ty; simpl; intros.
+ remember (store_stack m (Vptr sp Int.zero) Tint
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in H. clear Heqs.
    destruct s; inv H. trivial.
+ remember (store_stack m (Vptr sp Int.zero) Tfloat
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in H. clear Heqs.
    destruct s; inv H. trivial.
+ destruct v; inv H.
  - remember (store_stack m (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(z+1)))
                            (Vint (Int64.hiword i))) as s1.
    unfold Stacklayout.fe_ofs_arg in Heqs1. simpl in Heqs1.
    rewrite <- Heqs1 in *. clear Heqs1.
    destruct s1; inv H1.
    remember (store_stack m0 (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*z))
                            (Vint (Int64.loword i))) as s2.
    unfold Stacklayout.fe_ofs_arg in Heqs2. simpl in Heqs2.
    rewrite <- Heqs2 in *. clear Heqs2.
    destruct s2; inv H0. trivial.
+ remember (store_stack m (Vptr sp Int.zero) Tsingle
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in *. clear Heqs.
    destruct s; inv H. trivial.
+ remember (store_stack m (Vptr sp Int.zero) Tany32
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in *. clear Heqs.
    destruct s; inv H. trivial.
+ remember (store_stack m (Vptr sp Int.zero) Tany64
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in *. clear Heqs.
    destruct s; inv H. trivial.
Qed.

Lemma store_args_cons m sp z v args ty tys m1 z1:
  store_arg m sp z ty v = Some(m1, z1) ->
  (exists m', store_args_rec m1 sp z1 args tys = Some m') ->
  exists m', store_args_rec m sp z (v :: args) (ty :: tys) = Some m'.
Proof. intros.
simpl. unfold store_arg in H.
destruct ty.
+ remember (store_stack m (Vptr sp Int.zero) Tint
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
+ remember (store_stack m (Vptr sp Int.zero) Tfloat
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
+ destruct v; inv H.
  - remember (store_stack m (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(z+1)))
                            (Vint (Int64.hiword i))) as s1.
    unfold Stacklayout.fe_ofs_arg in Heqs1. simpl in Heqs1.
    rewrite <- Heqs1 in *. clear Heqs1.
    destruct s1; inv H2.
    remember (store_stack m0 (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*z))
                            (Vint (Int64.loword i))) as s2.
    unfold Stacklayout.fe_ofs_arg in Heqs2. simpl in Heqs2.
    rewrite <- Heqs2 in *. clear Heqs2.
    destruct s2; inv H1. assumption.
+ remember (store_stack m (Vptr sp Int.zero) Tsingle
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
+ remember (store_stack m (Vptr sp Int.zero) Tany32
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
+ remember (store_stack m (Vptr sp Int.zero) Tany64
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
Qed.

Lemma store_arg_perm1: forall m sp z ty v mm zz
      (STA: store_arg m sp z ty v = Some (mm, zz)),
       forall (b' : block) (ofs' : Z) (k : perm_kind) (p : permission),
       Mem.perm m b' ofs' k p -> Mem.perm mm b' ofs' k p.
Proof. intros.
simpl. unfold store_arg in STA.
destruct ty.
+ remember (store_stack m (Vptr sp Int.zero) Tint
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs.
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
+ remember (store_stack m (Vptr sp Int.zero) Tfloat
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs.
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
+ destruct v; inv STA.
  - remember (store_stack m (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(z+1)))
                            (Vint (Int64.hiword i))) as s1.
    unfold Stacklayout.fe_ofs_arg in Heqs1. simpl in Heqs1.
    rewrite <- Heqs1 in *. apply eq_sym in Heqs1.
    destruct s1; inv H1.
    remember (store_stack m0 (Vptr sp Int.zero) Tint
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*z))
                            (Vint (Int64.loword i))) as s2.
    unfold Stacklayout.fe_ofs_arg in Heqs2. simpl in Heqs2.
    rewrite <- Heqs2 in *. apply eq_sym in Heqs2.
    destruct s2; inv H2.
    unfold store_stack in *; simpl in *.
    eapply Mem.perm_store_1; try eassumption.
    eapply Mem.perm_store_1; eassumption.
+ remember (store_stack m (Vptr sp Int.zero) Tsingle
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs.
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
+ remember (store_stack m (Vptr sp Int.zero) Tany32
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs.
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
+ remember (store_stack m (Vptr sp Int.zero) Tany64
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs.
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
Qed.

Lemma store_args_rec_succeeds_aux sp:
  forall tys args
      (VALSDEF: val_casted.vals_defined args=true)
      (HASTY: Val.has_type_list args tys) sz
      (ALR: args_len_rec args tys = Some sz)
      z (POS: 0 <= z)
      (REP: 4*(z+sz) < Int.modulus) m
      (RP: Mem.range_perm m sp (4*z) (4*z + 4*sz) Cur Writable),
  exists m', store_args_rec m sp z args tys = Some m'.
Proof.
intros tys. induction tys.
+ intros.
  destruct args; simpl in *; inv ALR. rewrite Zplus_0_r in *.
     eexists; reflexivity.
+ destruct args. intros. inv ALR.
  intros. destruct HASTY.
  assert (ArgsDef: vals_defined args = true).
    destruct v; try inv VALSDEF; trivial.
 apply args_len_recD in ALR.
 destruct ALR as [sizeA [sz' [SZ [AL SzA]]]].
 assert (sizeA = typesize a).
 { clear - SzA H. destruct a; try solve[trivial]. simpl. admit. (*TODO (Gordon?): In CompCert 2.6, this assert is not true any longer*) }
 clear SzA.
 subst sz sizeA.
 assert (STARG: exists mm zz, store_arg m sp z a v = Some(mm,zz)).
 { clear IHtys H0.
   destruct (typ_eq a Tlong). subst a.
   { simpl. destruct v; try solve[simpl in VALSDEF; congruence | inv H].
     assert (H1: sz' >= 0) by (apply args_len_rec_nonneg in AL; omega).
     destruct (Mem.valid_access_store m (chunk_of_type Tint) sp (4*(z+1)) (Vint (Int64.hiword i)))
       as [mm ST].
      split. red; intros. eapply RP; clear RP.
        split. omega.
        assert (1 + size_chunk (chunk_of_type Tint) <= 4 * (typesize Tlong + sz')).
         { clear - AL. apply args_len_rec_nonneg in AL.
           unfold typesize. simpl size_chunk. omega. }
        destruct H0. simpl size_chunk in H3. simpl typesize. clear - H1 H3. omega.
        clear - POS. rewrite Zmult_comm. solve[simpl align_chunk; eapply Zdivide_intro; eauto].
     destruct (Mem.valid_access_store mm (chunk_of_type Tint) sp (4*z) (Vint (Int64.loword i)))
       as [mm' ST'].
      split. red; intros.
        eapply Mem.perm_store_1; eauto.
        eapply RP; eauto. clear RP. split. omega.
        assert (size_chunk (chunk_of_type Tint) <= 4 * (typesize Tlong + sz')).
         { clear - AL. apply args_len_rec_nonneg in AL.
           unfold typesize. simpl size_chunk. omega. }
        destruct H0. simpl size_chunk in H3. simpl typesize. clear - H1 H3. omega.
        clear - POS. rewrite Zmult_comm. solve[simpl align_chunk; eapply Zdivide_intro; eauto].
     unfold store_stack. simpl. simpl in ST, ST'.
     assert (A: 0 <= 4*(z+1) <= Int.max_unsigned).
     { split. omega. simpl typesize in REP.
       assert (1 + sz' >= 0) by (apply args_len_rec_nonneg in AL; omega).
       unfold Int.max_unsigned. omega. }
     assert (B: 0 <= 4*z <= Int.max_unsigned) by omega.
     rewrite !Int.add_zero_l, !Int.unsigned_repr, ST, ST'.
       exists mm', (z+2); trivial. solve[apply B]. solve[apply A]. }
   destruct (Mem.valid_access_store m (chunk_of_type a) sp (4*z) v) as [mm ST].
    split. red; intros. eapply RP; clear RP.
        split. omega.
        assert (size_chunk (chunk_of_type a) <= 4 * (typesize a + sz')).
         { clear - AL. apply args_len_rec_nonneg in AL.
            unfold typesize. destruct a; simpl in *.
               destruct sz'; xomega. destruct sz'. xomega.
               destruct p; xomega. xomega.
               destruct sz'; try xomega. destruct p; xomega.
               destruct sz'; try xomega.
               destruct sz'; try xomega.
               destruct sz'; try xomega.
               destruct p; try xomega.  }
         remember (size_chunk (chunk_of_type a)) as p1.
         remember (typesize a + sz') as p2. clear - H0 H1. omega.
      clear - POS n. rewrite Zmult_comm.
      destruct a; simpl align_chunk; eapply Zdivide_intro; eauto. congruence.
   clear RP.
   destruct a; simpl in ST; simpl.
    - unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST.
       exists mm, (z+1); trivial.
       assert (A: 0 <= 4*z <= Int.max_unsigned).
       { split. omega. simpl typesize in REP.
         assert (1 + sz' >= 0) by (apply args_len_rec_nonneg in AL; omega).
         unfold Int.max_unsigned. omega. }
       solve[apply A].
    - unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST.
       exists mm, (z+2); trivial.
       clear - POS REP AL.
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega.
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tfloat + sz').
           simpl. destruct sz'. omega. xomega. xomega.
         remember (typesize Tfloat + sz') as q. clear  AL Heqq sz'.
           unfold Int.max_unsigned. xomega.
    - congruence.
    - unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST.
       exists mm, (z+1); trivial.
       clear - POS REP AL.
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega.
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tsingle + sz').
           simpl. destruct sz'. omega. xomega. xomega.
         remember (typesize Tsingle + sz') as q. clear  AL Heqq sz'.
           unfold Int.max_unsigned. xomega.
    - unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST.
       exists mm, (z+1); trivial.
       clear - POS REP AL.
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega.
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tany32 + sz').
           simpl. destruct sz'. omega. xomega. xomega.
         remember (typesize Tany32 + sz') as q. clear  AL Heqq sz'.
           unfold Int.max_unsigned. xomega.
    - unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST.
       exists mm, (z+2); trivial.
       clear - POS REP AL.
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega.
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tany64 + sz').
           simpl. destruct sz'. omega. xomega. xomega.
         remember (typesize Tany64 + sz') as q. clear  AL Heqq sz'.
           unfold Int.max_unsigned. xomega.
 }
 specialize (IHtys _ ArgsDef H0 _ AL).
 rewrite Zplus_assoc in REP.
 assert (POS' : 0 <= z+typesize a). destruct a; simpl; omega.
 specialize (IHtys _ POS' REP).
 destruct STARG as [mm [zz STARG]].
 specialize (store_argSZ _ _ _ _ _ _ _ STARG). intros ZZ; subst zz.
 eapply store_args_cons. eassumption.
 apply IHtys; clear IHtys.
 red; intros. eapply store_arg_perm1; eauto.
 clear STARG. eapply RP; clear RP.
 specialize (typesize_pos a); intros. omega.
(*FIXME: *) Grab Existential Variables. refine (0).
Admitted. (*TODO: (End of proof containing the now incorrect typesize assertion)*)

Lemma store_args_rec_succeeds sz m sp args tys
      (VALSDEF: val_casted.vals_defined args=true)
      (HASTY: Val.has_type_list args tys)
      (REP: 4*sz < Int.modulus) m'' :
  args_len_rec args tys = Some sz ->
  Mem.alloc m 0 (4*sz) = (m'',sp) ->
  exists m', store_args_rec m'' sp 0 args tys = Some m'.
Proof.
intros H H2. exploit store_args_rec_succeeds_aux; eauto. omega. omega.
intros ofs [H3 H4]. apply Mem.perm_alloc_2 with (ofs := ofs) (k := Cur) in H2; auto.
eapply Mem.perm_implies; eauto. constructor.
Qed.

Definition store_args m sp args tys := store_args_rec m sp 0 args tys.

Require Import ccc26x86.Conventions1.

(*Fixpoint agree_args_contains_aux m' sp' ofs args tys : Prop :=
  match args,tys with
    | nil,nil => True
    | a::args',ty::tys' =>
        Mem.load (chunk_of_type ty) m' sp' (fe_ofs_arg + 4*ofs) = Some a
        /\ agree_args_contains_aux m' sp' (ofs+1) args' tys'
    | _,_ => False
  end.*)

Fixpoint agree_args_contains_aux m' sp' ofs args tys : Prop :=
  let vsp := Vptr sp' Int.zero in
  match tys with
    | nil => args=nil
    | ty'::tys' =>
      match args with
        | nil => False
        | a'::args' =>
          match ty' with
            | Tlong =>
              match a' with
                | Vlong n =>
                  load_stack m' vsp Tint (Int.repr (4*(ofs+1)))
                  = Some (Vint (Int64.hiword n))
                  /\ load_stack m' vsp Tint (Int.repr (4*ofs))
                     = Some (Vint (Int64.loword n))
                  /\ agree_args_contains_aux m' sp' (ofs+2) args' tys'
                | _ => False
              end
            | _ =>
              load_stack m' vsp ty' (Int.repr (4*ofs)) = Some a'
              /\ agree_args_contains_aux m' sp' (ofs+typesize ty') args' tys'
          end
      end
  end.

Lemma agree_args_contains_aux_invariant:
  forall tys m sp ofs args m',
  agree_args_contains_aux m sp ofs args tys ->
  Mem.unchanged_on (fun b ofs => b=sp) m m' ->
  agree_args_contains_aux m' sp ofs args tys.
Proof.
induction tys. destruct args; simpl; auto.
intros m'; destruct args; simpl; auto. destruct a.
+ generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z.
  intros z [H H2] [H3 H4]. split; eauto.
  unfold load_stack, Mem.loadv in H3|-*.
  revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z));
    try solve[inversion 1].
  simpl; intros ? ?; inversion 1; subst.
  eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
+ generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z.
  intros z [H H2] [H3 H4]. split; eauto.
  unfold load_stack, Mem.loadv in H3|-*.
  revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z));
    try solve[inversion 1].
  simpl; intros ? ?; inversion 1; subst.
  eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
+ generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z.
  generalize
     (Int.repr
        match ofs + 1 with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z1.
  destruct v; try inversion 3.
  intros z1 z [H H2] [H3 [H4 H5]]. split; eauto.
  unfold load_stack, Mem.loadv in H3|-*.
  revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z));
    try solve[inversion 1].
  simpl; intros ? ?; inversion 1; subst.
  eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
  split. eapply Mem.load_unchanged_on; eauto. intros. solve[simpl; auto].
  solve[eapply IHtys; eauto].
+ generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z.
  intros z [H H2] [H3 H4]. split; eauto.
  unfold load_stack, Mem.loadv in H3|-*.
  revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z));
    try solve[inversion 1].
  simpl; intros ? ?; inversion 1; subst.
  eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
+ generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z.
  intros z [H H2] [H3 H4]. split; eauto.
  unfold load_stack, Mem.loadv in H3|-*.
  revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z));
    try solve[inversion 1].
  simpl; intros ? ?; inversion 1; subst.
  eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
+ generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z.
  intros z [H H2] [H3 H4]. split; eauto.
  unfold load_stack, Mem.loadv in H3|-*.
  revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z));
    try solve[inversion 1].
  simpl; intros ? ?; inversion 1; subst.
  eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
Qed.

Lemma args_len_rec_bound args tys z :
  args_len_rec args tys = Some z -> z <= 2*Zlength args.
Proof.
  revert args z. induction tys. destruct args. simpl. inversion 1; omega.
  simpl. inversion 1. destruct args. inversion 1. intros z H.
  apply args_len_recD in H. destruct H as [z1 [z2 [Zeq [? H2]]]]. subst z.
  specialize (IHtys _ _ H). destruct a; subst z1; rewrite Zlength_cons; omega.
Qed.

Lemma store_args_inject args args' tys j m m' m2 m2' b b' z :
  Val.inject_list j args args' ->
  Mem.inject j m m' ->
  j b = Some (b',0) ->
  store_args_rec m b z args tys = Some m2 ->
  store_args_rec m' b' z args' tys = Some m2' ->
  Mem.inject j m2 m2'.
Proof.
intros A B C D E.
revert args args' m m' z A B D E. induction tys.
intros args args' m m' z H. inv H. simpl.
  inversion 2; subst. solve[inversion 1; subst; auto].
intros ? ?; inversion 1.
intros ? ? ? ? ?. intros H. inv H. solve[inversion 2]. simpl. intros H.
generalize
 (Int.repr match z with
             | 0 => 0 | Z.pos y' => Z.pos y'~0~0
             | Z.neg y' => Z.neg y'~0~0 end) as z'.
generalize
 (Int.repr match z+1 with
             | 0 => 0 | Z.pos y' => Z.pos y'~0~0
             | Z.neg y' => Z.neg y'~0~0 end) as z''.
intros z'' z'. destruct a.
- case_eq (store_stack m (Vptr b Int.zero) Tint z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H2.
exploit Mem.store_mapped_inject; try eassumption.
intros [m0' [STORE' INJ]].
rewrite Zplus_0_r in STORE'. rewrite STORE'. intros H3.
eapply IHtys; eauto.
- case_eq (store_stack m (Vptr b Int.zero) Tfloat z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H2.
exploit Mem.store_mapped_inject; try eassumption.
intros [m0' [STORE' INJ]].
rewrite Zplus_0_r in STORE'. rewrite STORE'. intros H3.
eapply IHtys; eauto.
- inv H0; try solve[inversion 1].
case_eq (store_stack m (Vptr b Int.zero) Tint z'' (Vint (Int64.hiword i)));
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H2.
exploit Mem.store_mapped_inject; eauto.
intros [m0' [STORE' INJ]].
rewrite Zplus_0_r in STORE'. rewrite STORE'.
revert H2. rewrite Int.add_zero_l.
case_eq (Mem.store Mint32 m0 b (Int.unsigned z') (Vint (Int64.loword i)));
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m1 STORE1 H3.
exploit Mem.store_mapped_inject; eauto.
intros [m1' [STORE1' INJ']]. rewrite Zplus_0_r in STORE1'. rewrite STORE1'.
eapply IHtys; eauto.
- case_eq (store_stack m (Vptr b Int.zero) Tsingle z' v);
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H2.
exploit Mem.store_mapped_inject; try eassumption. eauto.
intros [m0' [STORE' INJ]].
rewrite Zplus_0_r in STORE'. rewrite STORE'. intros H3.
eapply IHtys; eauto.
- case_eq (store_stack m (Vptr b Int.zero) Tany32 z' v);
  try solve[intros; congruence].
  unfold store_stack, Mem.storev. simpl. intros m0 STORE H2.
  exploit Mem.store_mapped_inject; try eassumption.
  intros [m0' [STORE' INJ]].
  rewrite Zplus_0_r in STORE'. rewrite STORE'. intros H3.
  eapply IHtys; eauto.
- case_eq (store_stack m (Vptr b Int.zero) Tany64 z' v);
  try solve[intros; congruence].
  unfold store_stack, Mem.storev. simpl. intros m0 STORE H2.
  exploit Mem.store_mapped_inject; try eassumption.
  intros [m0' [STORE' INJ]].
  rewrite Zplus_0_r in STORE'. rewrite STORE'. intros H3.
  eapply IHtys; eauto.
Qed.

Lemma args_len_rec_inject j args args' tys z z' :
  Val.inject_list j args args' ->
  args_len_rec args tys = Some z ->
  args_len_rec args' tys = Some z' ->
  z=z'.
Proof.
intros.
revert tys z z' H0 H1.
induction H.
simpl. destruct tys; inversion 1. inversion 1; subst; auto.
destruct tys; inversion 1. simpl. destruct t.
+ inv H1.
revert H3 H4.
case_eq (args_len_rec vl tys); try solve[intros; congruence]. intros.
revert H2. case_eq (args_len_rec vl' tys); try solve[intros; congruence]. intros.
exploit IHinject_list; eauto.
intros. subst z0. inv H3; inv H4; inv H5. omega.
+ inv H1.
revert H3 H4.
case_eq (args_len_rec vl tys); try solve[intros; congruence]. intros.
revert H2. case_eq (args_len_rec vl' tys); try solve[intros; congruence]. intros.
exploit IHinject_list; eauto.
intros. subst z0. inv H3; inv H4; inv H5. omega.
+ inv H1.
revert H3 H4.
destruct v; try solve[inversion 1].
destruct v'; try solve[inversion 3].
case_eq (args_len_rec vl tys); try solve[inversion 2].
case_eq (args_len_rec vl' tys); try solve[intros; congruence]. intros.
exploit IHinject_list; eauto.
intros. subst z0. inv H3; inv H4; inv H5. omega.
+ inv H1.
revert H3 H4.
case_eq (args_len_rec vl tys); try solve[intros; congruence]. intros.
revert H2. case_eq (args_len_rec vl' tys); try solve[intros; congruence]. intros.
exploit IHinject_list; eauto.
intros. subst z0. inv H3; inv H4; inv H5. omega.
+ inv H1.
revert H3 H4.
case_eq (args_len_rec vl tys); try solve[intros; congruence]. intros.
revert H2. case_eq (args_len_rec vl' tys); try solve[intros; congruence]. intros.
exploit IHinject_list; eauto.
intros. subst z0. inv H3; inv H4; inv H5. omega.
+ inv H1.
revert H3 H4.
case_eq (args_len_rec vl tys); try solve[intros; congruence]. intros.
revert H2. case_eq (args_len_rec vl' tys); try solve[intros; congruence]. intros.
exploit IHinject_list; eauto.
intros. subst z0. inv H3; inv H4; inv H5. omega.
Qed.

Lemma sm_locally_allocated_only_stores1 mu mu' b1 l1 m1 m2 m1' m2' m1'' :
  mem_forward m1 m1' ->
  sm_locally_allocated mu mu' m1 m2 m1' m2' ->
  only_stores b1 l1 m1' m1'' ->
  sm_locally_allocated mu mu' m1 m2 m1'' m2'.
Proof.
intros.
revert m2 m2' mu mu' H H0. induction X; auto. intros.
apply IHX.
eapply mem_forward_trans; eauto. apply store_forward in e. auto. auto.
rewrite sm_locally_allocatedChar in H0|-*.
destruct H0 as [? [? [? [? [? ?]]]]].
intuition.
generalize e as e'. intro.
apply store_freshloc in e. rewrite H0.
extensionality b. destruct (DomSrc mu b); auto. simpl.
symmetry. rewrite <-freshloc_trans with (m'':= m); auto. rewrite e.
  solve[rewrite orb_comm; auto].
apply store_forward in e'. eauto.
rewrite H2. extensionality b. destruct (locBlocksSrc mu b); simpl; auto.
generalize e as e'. intro.
apply store_freshloc in e.
symmetry. rewrite <-freshloc_trans with (m'':= m); auto. rewrite e.
  solve[rewrite orb_comm; auto].
apply store_forward in e'. eauto.
Qed.

Lemma sm_locally_allocated_only_stores2 mu mu' b2 l2 m1 m2 m1' m2' m2'' :
  mem_forward m2 m2' ->
  sm_locally_allocated mu mu' m1 m2 m1' m2' ->
  only_stores b2 l2 m2' m2'' ->
  sm_locally_allocated mu mu' m1 m2 m1' m2''.
Proof.
intros.
revert m1 m1' mu mu' H H0. induction X; auto. intros.
apply IHX; auto.
eapply mem_forward_trans; eauto. apply store_forward in e. auto.
rewrite sm_locally_allocatedChar in H0|-*.
destruct H0 as [? [? [? [? [? ?]]]]].
intuition.
generalize e as e'. intro.
apply store_freshloc in e. rewrite H1.
extensionality b. destruct (DomTgt mu b); auto. simpl.
symmetry. rewrite <-freshloc_trans with (m'':= m); auto. rewrite e.
  solve[rewrite orb_comm; auto].
apply store_forward in e'. eauto.
rewrite H3. extensionality b. destruct (locBlocksTgt mu b); simpl; auto.
generalize e as e'. intro.
apply store_freshloc in e.
symmetry. rewrite <-freshloc_trans with (m'':= m); auto. rewrite e.
  solve[rewrite orb_comm; auto].
apply store_forward in e'. eauto.
Qed.

Lemma sm_locally_allocated_only_stores mu mu' b1 b2 l1 l2 m1 m2 m1' m2' m1'' m2'' :
  mem_forward m1 m1' ->
  mem_forward m2 m2' ->
  sm_locally_allocated mu mu' m1 m2 m1' m2' ->
  only_stores b1 l1 m1' m1'' ->
  only_stores b2 l2 m2' m2'' ->
  sm_locally_allocated mu mu' m1 m2 m1'' m2''.
Proof.
intros.
eapply sm_locally_allocated_only_stores1; eauto.
eapply sm_locally_allocated_only_stores2; eauto.
Qed.

Lemma sm_valid_only_stores mu b1 b2 l1 l2 m1 m2 m1' m2' :
  sm_valid mu m1 m2 ->
  only_stores b1 l1 m1 m1' ->
  only_stores b2 l2 m2 m2' ->
  sm_valid mu m1' m2'.
Proof.
revert m2 m2' b2 l2 mu; induction 2. induction 1; auto.
apply Mem.nextblock_store in e.
apply IHX. unfold sm_valid. unfold Mem.valid_block. rewrite e.
destruct H. split; auto.
intros. apply IHX; auto. apply Mem.nextblock_store in e.
destruct H. unfold sm_valid, Mem.valid_block. rewrite e. auto.
Qed.

Lemma REACH_only_stores b l m m' roots :
  only_stores b l m m' ->
  roots b = true ->
  (forall b' : block,
     getBlocks l b' = true -> roots b' = true) ->
  REACH_closed m roots ->
  REACH_closed m' roots.
Proof.
induction 1; auto. intros H H2 H3. apply IHX; auto.
intros. apply H2. rewrite getBlocksD. destruct v; auto.
  solve[rewrite orb_true_iff; auto].
eapply REACH_Store; eauto.
intros. eapply H2. rewrite getBlocksD in H0|-*.
destruct v; auto; try solve[rewrite getBlocksD_nil in H0; congruence].
rewrite getBlocksD_nil, orb_comm in H0; simpl in H0.
rewrite H0; auto.
Qed.

Lemma store_stack_mem m sp ty ofs v m'
        (ST: store_stack m sp ty ofs v = Some m'):
      mem_step m m'.
Proof. intros.
 unfold store_stack in ST. destruct sp; simpl in ST; inv ST.
 eapply mem_step_store; eassumption.
Qed.

Lemma store_args_mem sp ofs args tys m m' :
  store_args_rec m sp ofs args tys = Some m' ->
  mem_step m m'.
Proof.
revert args ofs m; induction tys.
+ destruct args.
  - intros ofs. inversion 1; subst. apply mem_step_refl.
  - intros ofs m. simpl. inversion 1.
+ destruct args; try solve[inversion 1].
  destruct a; simpl; intros ofs m.
  - case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
    * intros.
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ H).
       eapply IHtys; eassumption.
    * intros; congruence.
  - case_eq (store_stack m (Vptr sp Int.zero) Tfloat
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
    * intros.
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ H).
       eapply IHtys; eassumption.
    * intros; congruence.
  - destruct v; try solve[congruence].
    case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                      | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.hiword i))).
    * intros.
       remember (store_stack m0 (Vptr sp Int.zero) Tint
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) (Vint (Int64.loword i))).
       symmetry in Heqo; destruct o; inv H0.
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ H).
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ Heqo).
      eapply IHtys; eassumption.
    * intros; congruence.
  - intros.
    remember (store_stack m (Vptr sp Int.zero) Tsingle
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) v).
       symmetry in Heqo; destruct o; inv H.
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ Heqo).
       eapply IHtys; eassumption.
  - intros.
    remember (store_stack m (Vptr sp Int.zero) Tany32
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) v).
       symmetry in Heqo; destruct o; inv H.
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ Heqo).
       eapply IHtys; eassumption.
  - intros.
    remember (store_stack m (Vptr sp Int.zero) Tany64
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) v).
       symmetry in Heqo; destruct o; inv H.
      eapply mem_step_trans.
       apply (store_stack_mem _ _ _ _ _ _ Heqo).
       eapply IHtys; eassumption.
Qed.

Lemma store_args_mem_step m stk args tys m':
  store_args m stk args tys = Some m' -> mem_step m m'.
Proof. intros. unfold store_args in H.
  apply store_args_rec_only_stores in H.
  remember (encode_longs tys args). clear Heql.
  induction H. apply mem_step_refl.
  eapply mem_step_trans; try eassumption.
  eapply mem_step_store; eassumption.
Qed.
