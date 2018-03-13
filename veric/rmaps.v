Require Import VST.msl.msl_standard.
Require Import VST.msl.ghost.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.shares.

Module Type ADR_VAL.
Parameter address : Type.
Parameter some_address:address.

(* Validity of traces.  The "valid" predicate ensures that related addresses don't get
    split apart from each other.  *)
Parameter kind: Type.
Parameter valid : (address -> option (rshare * kind)) -> Prop.
Parameter valid_empty: valid (fun _ => None).
Parameter valid_join: forall f g h : address -> option (rshare * kind),
   @join _ (Join_fun address (option (rshare * kind))
                   (Join_lower (Join_prod rshare Join_rshare kind (Join_equiv kind))))
      f g h  ->
 valid f -> valid g -> valid h.
End ADR_VAL.

Module Type ADR_VAL0.
Parameter address : Type.
Parameter some_address:address.
Parameter kind: Type.
End ADR_VAL0.

Module SimpleAdrVal (AV0: ADR_VAL0) <:
   ADR_VAL with Definition address := AV0.address
                   with Definition kind := AV0.kind.
  Import AV0.
  Definition address := address.
  Definition some_address := some_address.
  Definition kind := kind.
  Definition valid (_: address -> option (rshare * kind)) := True.
  Lemma valid_empty: valid (fun _ => None).
  Proof. unfold valid; auto. Qed.
  Lemma valid_join: forall f g h : address -> option (rshare * kind),
   @join _ (Join_fun address (option (rshare * kind))
                   (Join_lower (Join_prod rshare Join_rshare kind (Join_equiv kind))))
      f g h  ->
    valid f -> valid g -> valid h.
  Proof.  intros; unfold valid; auto. Qed.
End SimpleAdrVal.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree.

Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor :=
  fix dtfr (T: TypeTree): functor :=
  match T with
  | ConstType A => fconst A
  | Mpred => fidentity
  | DependentType n => fconst (nth n ts unit)
  | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
  | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
  | PiType _ f => fpi (fun i => dtfr (f i))
  end.
Opaque dependent_type_functor_rec.

Definition dependent_type_function_rec (ts: list Type) (mpred': Type): TypeTree -> Type :=
  fix dtfr (T: TypeTree): Type :=
  match T with
  | ConstType A => A
  | Mpred => mpred'
  | DependentType n => nth n ts unit
  | ProdType T1 T2 => (dtfr T1 * dtfr T2)%type
  | ArrowType T1 T2 => dtfr T1 -> dtfr T2
  | PiType A f => forall a, dtfr (f a)
  end.

Definition fpreds: functor :=
  fsig (fun T: TypeTree =>
    fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

Instance preds_join (PRED : Type) (I: Type) : Join (I -> nat -> option (fpreds PRED)) :=
  Join_fun _ _ (Join_fun _ _ (Join_lower (Join_equiv (fpreds PRED)))).

Section Finmap.

(* There are a million ways to define a finite map. I want one that:
   can be used generically (so cannot defined as a module),
   provides a function that returns a fresh index,
   and has extensional equivalence as its equality. *)
Definition finmap A := list (option A).

Import ListNotations.
Definition finmap_set {A} (m : finmap A) k v : finmap A :=
  firstn k m ++ repeat None (k - length m) ++ Some v :: skipn (S k) m.

Definition finmap_get {A} (m : finmap A) k := nth k m None.

Lemma nth_firstn: forall {A} m (l : list A) n d, m < length (firstn n l) ->
  nth m (firstn n l) d = nth m l d.
Proof.
  induction m; destruct l, n; auto; simpl; intros; try omega.
  apply IHm; omega.
Qed.

Lemma nth_repeat: forall {A} m n (x : A), nth m (repeat x n) x = x.
Proof.
  induction m; destruct n; simpl; intros; auto.
Qed.

Lemma nth_nil: forall {A} n (d : A), nth n [] d = d.
Proof.
  destruct n; auto.
Qed.

Lemma nth_skipn: forall {A} n m (l : list A) d, nth m (skipn n l) d = nth (m + n) l d.
Proof.
  induction n; simpl; intros.
  { rewrite Nat.add_0_r; auto. }
  destruct l.
  { rewrite !nth_nil; auto. }
  rewrite IHn, Nat.add_succ_r; auto.
Qed.

Opaque skipn.

Lemma finmap_get_empty: forall {A} i, finmap_get (@nil (option A)) i = None.
Proof.
  intros; apply nth_nil.
Qed.

Lemma finmap_get_set: forall {A} (m : finmap A) j k v,
  finmap_get (finmap_set m k v) j = if eq_dec j k then Some v else finmap_get m j.
Proof.
  intros; unfold finmap_get, finmap_set.
  destruct (eq_dec j k).
  - subst.
    rewrite 2app_nth2; rewrite ?firstn_length, ?repeat_length.
    replace (_ - _) with O; auto.
    all: destruct (Min.min_spec k (length m)) as [[? ->] | [? ->]]; auto; omega.
  - destruct (lt_dec j (length (firstn k m))).
    { rewrite app_nth1, nth_firstn; auto. }
    rewrite app_nth2 by omega.
    rewrite firstn_length in *.
    destruct (lt_dec k (length m)).
    + rewrite Min.min_l in * by omega.
      replace (k - length m) with O by omega.
      destruct (j - k) eqn: Hminus; [omega | simpl].
      rewrite nth_skipn.
      f_equal; omega.
    + rewrite Min.min_r in * by omega.
      rewrite (nth_overflow m) by omega.
      destruct (lt_dec (j - length m) (k - length m)).
      { rewrite app_nth1, nth_repeat; auto.
        rewrite repeat_length; auto. }
      rewrite app_nth2; rewrite repeat_length; [|omega].
      destruct (j - length m - (k - length m)) eqn: Hminus; [omega | simpl].
      rewrite nth_skipn, nth_overflow; auto; omega.
Qed.

Definition fresh {A} (m : finmap A) := length m.
Lemma fresh_spec: forall {A} (m : finmap A), finmap_get m (fresh m) = None.
Proof.
  unfold fresh, finmap_get; intros; rewrite nth_overflow; auto.
Qed.


Context {A} {J: Join A}.

Inductive finmap_join: Join (finmap A) :=
| finmap_join_nil_l m: finmap_join [] m m
| finmap_join_nil_r m: finmap_join m [] m
| finmap_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> finmap_join m1 m2 m3 ->
    finmap_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
Hint Constructors finmap_join.

Lemma finmap_join_inv: forall m1 m2 m3, finmap_join m1 m2 m3 ->
  match m1, m2 with
  | [], _ => m3 = m2
  | _, [] => m3 = m1
  | a1 :: m1, a2 :: m2 => match m3 with [] => False
                          | a3 :: m3 => join a1 a2 a3 /\ finmap_join m1 m2 m3 end
  end.
Proof.
  induction 1; simpl; auto.
  destruct m; simpl; auto.
Qed.

Lemma finmap_get_join: forall m1 m2 m3, finmap_join m1 m2 m3 -> forall i,
  match finmap_get m1 i, finmap_get m2 i, finmap_get m3 i with
  | Some a1, Some a2, Some a3 => join a1 a2 a3
  | None, x, y | x, None, y => y = x
  | _, _, _ => False
  end.
Proof.
  unfold finmap_get; induction 1; intros; rewrite ?nth_nil; auto.
  { destruct (nth i m None); auto. }
  destruct i; simpl.
  - inv H; auto.
    destruct a3; auto.
  - apply IHfinmap_join.
Qed.

(* Note that maps are not a Disj_alg, since a map containing only cores joins with itself
   but isn't a universal unit. *)
Global Instance Perm_finmap {P: Perm_alg A} : @Perm_alg _ finmap_join.
Proof.
  constructor.
  - intros until 1; revert z'; induction H; inversion 1; subst; auto.
    f_equal; auto.
    eapply join_eq; eauto.
  - unfold join; simpl.
    induction a; intros ???? HJ1 HJ2; apply finmap_join_inv in HJ1; subst; eauto.
    destruct b; subst; eauto.
    destruct d; [contradiction|].
    destruct HJ1 as [Ha1 HJ1].
    apply finmap_join_inv in HJ2; simpl in HJ2.
    destruct c; subst; eauto.
    destruct e; [contradiction|].
    destruct HJ2 as [Ha2 HJ2].
    destruct (join_assoc Ha1 Ha2) as (f & ? & ?).
    destruct (IHa _ _ _ _ HJ1 HJ2) as (f' & ? & ?).
    exists (f :: f'); auto.
  - induction 1; constructor; auto.
  - intros until 1; revert b'; induction H; inversion 1; subst; auto.
    f_equal; eauto.
    eapply join_positivity; eauto.
Qed.

Global Instance Sep_finmap {S: Sep_alg A} : @Sep_alg _ finmap_join.
Proof.
  exists (fun _ => nil); auto.
  constructor.
Qed.

End Finmap.

Instance finmap_RA {RA: Ghost} : Ghost :=
  { valid m := forall i a, finmap_get m i = Some a -> valid a; Join_G := finmap_join }.
Proof.
  intros.
  specialize (H0 i).
  apply finmap_get_join with (i0 := i) in H.
  rewrite H1 in H.
  destruct (finmap_get b i); eauto.
  destruct (finmap_get c i); [|contradiction].
  eapply join_valid; eauto.
Defined.

Existing Instance finmap_join.

Instance Global_Ghost {I} {RAs: I -> Ghost}: Ghost :=
  { G := forall i, finmap (@G (RAs i)); valid m := forall i, @valid finmap_RA (m i) }.
Proof.
  intros.
  specialize (H i).
  eapply join_valid; eauto.
Defined.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
  Import AV.

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> fpreds PRED -> res PRED
    | PURE': kind -> fpreds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh nsh => NO' B rsh nsh
      | YES' sh rsh k pds => YES' B sh rsh k (fmap fpreds f g pds)
      | PURE' k pds => PURE' B k (fmap fpreds f g pds)
    end.
  Axiom ff_res : functorFacts res res_fmap.
  Definition f_res : functor := Functor ff_res.

  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (NO' PRED sh2 nsh2) 
                                     (NO' PRED sh3 nsh3)
    | res_join_NO2 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (YES' PRED sh2 rsh2 k p) 
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_NO3 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (YES' PRED sh1 rsh1 k p) (NO' PRED sh2 nsh2) 
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p,
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED sh1 rsh1 k p) (YES' PRED sh2 rsh2 k p) (YES' PRED sh3 rsh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).
  Axiom pa_rj : forall PRED, @Perm_alg _ (res_join PRED).
  Instance sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
  Proof. intros.
            apply mkSep 
             with (fun x => match x 
                             with NO' _ _ => NO' _ Share.bot bot_unreadable
                               | YES' _ _ _ _ => NO' _ Share.bot bot_unreadable
                               | PURE' k pds => PURE' _ k pds end).
            intro. destruct t; constructor; try apply join_unit1; auto.
            intros. inversion H; auto.
  Defined.

  Axiom paf_res : @pafunctor f_res res_join.

  Definition res_option (PRED : Type) (r: res PRED) : option (rshare * kind):=
    match r with
      | NO' _ _ => None
      | YES' sh rsh k _ => Some (readable_part rsh,k)
      | PURE' _ _ => None (* PUREs cannot be split in any interesting way, which is what valid is about. *)
    end.

  Inductive ghost (PRED : Type) : Type :=
    GHOST' I (RAs: I -> Ghost) (g: @G Global_Ghost) (pds: I -> nat -> option (fpreds PRED))
      (Hv: ghost.valid g)
      (dom: forall i n pp, pds i n = Some pp -> exists a, finmap_get (g i) n = Some a).

  Program Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    match x with
      | GHOST' _ RAs a pds _ _ =>
        GHOST' _ _ RAs a (fmap (ffunc (fconst _) (ffunc (fconst _) (foption fpreds))) f g pds) _ _
    end.
  Next Obligation.
  Proof.
    simpl in H.
    destruct (pds i n) eqn: Hi; inv H; eauto.
  Defined.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
  Definition f_ghost : functor := Functor ff_ghost.

  (* Will this give us the higher-order ghost state we want? *)
  Inductive ghost_join (PRED : Type) : Join (f_ghost PRED) :=
    | ghost_join_I : forall A (RAs : A -> Ghost) a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc,
        join a b c -> join pdsa pdsb pdsc ->
        ghost_join PRED (GHOST' PRED _ RAs a pdsa Hva doma) (GHOST' PRED _ RAs b pdsb Hvb domb)
                        (GHOST' PRED _ RAs c pdsc Hvc domc).

  Lemma ghost_ext: forall PRED I RAs g g' pds pds' Hv Hv' dom dom',
    g = g' -> pds = pds' -> GHOST' PRED I RAs g pds Hv dom = GHOST' PRED I RAs g' pds' Hv' dom'.
  Proof.
    intros; subst.
    f_equal; apply proof_irr.
  Qed.

  Axiom pa_gj : forall PRED, @Perm_alg _ (ghost_join PRED).

  Lemma core_dom: forall {PRED I} {RAs: I -> Ghost} (pds : I -> nat -> option (fpreds PRED))
    (g: @G Global_Ghost) i n pp, core pds i n = Some pp -> exists a, finmap_get (g i) n = Some a.
  Proof.
    discriminate.
  Qed.

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
  Proof.
    intros.
    exists (fun x => match x with GHOST' _ RA g pds Hv _ =>
                         GHOST' PRED _ RA (core g) (core pds) (core_valid _ Hv) (core_dom _ _) end).
    - destruct t; constructor; apply core_unit.
    - intros; inv H.
      apply ghost_ext; auto.
      eapply join_core; eauto.
  Defined.
  Axiom paf_ghost : @pafunctor f_ghost ghost_join.

  Definition valid' A (w: (address -> res A) * ghost A) : Prop :=
    AV.valid (fun l => res_option A (fst w l)).

  Axiom valid'_res_map : forall A B f g m,
    valid' A m -> valid' B (fmap f_res f g oo fst m, fmap f_ghost f g (snd m)).

  Definition f_pre_rmap : functor :=
    fsubset (fpair (ffunc (fconst address) f_res) f_ghost) _ valid'_res_map.

  Axiom valid'_res_map2 : forall A B f g m,
    valid' B (fmap f_res f g oo fst m, fmap f_ghost f g (snd m)) -> valid' A m.

  Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A) :=
            Join_prop _ (Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A)) (valid' A).

  Parameter Perm_pre_rmap: forall (A: Type), Perm_alg (f_pre_rmap A).
  Parameter Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

  Existing Instance ghost_join.
  Instance Join_res A : Join (f_res A) := res_join A.
  Axiom pre_rmap_core: forall A (m : f_pre_rmap A),
    exists P, core m = exist (valid' A) (core (proj1_sig m)) P.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.

  Definition preds: functor :=
    fsig (fun T: TypeTree =>
      fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh nsh => NO' B rsh nsh
      | YES' sh rsh k pds => YES' B sh rsh k (fmap preds f g pds)
      | PURE' k pds => PURE' B k (fmap preds f g pds)
    end.

  Lemma ff_res : functorFacts res res_fmap.
  Proof with auto.
    constructor; intros; extensionality rs; icase rs; unfold res_fmap.
    rewrite fmap_id... rewrite fmap_id...
    rewrite <- fmap_comp... rewrite <- fmap_comp...
  Qed.

  Definition f_res : functor := Functor ff_res.

  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (NO' PRED sh2 nsh2) 
                                     (NO' PRED sh3 nsh3)
    | res_join_NO2 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (YES' PRED sh2 rsh2 k p) 
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_NO3 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (YES' PRED sh1 rsh1 k p) (NO' PRED sh2 nsh2) 
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p,
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED sh1 rsh1 k p) (YES' PRED sh2 rsh2 k p) (YES' PRED sh3 rsh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).

  Instance Join_res (PRED: Type) : Join (res PRED) := res_join PRED.

  Instance pa_rj : forall PRED, @Perm_alg _ (res_join PRED).
  Proof. intros. constructor.
*      (* saf_eq *)
      intros x y z z' H1 H2; inv H1; inv H2;
      repeat match goal with H: join ?A ?B _, H': join ?A ?B ?C |- _ => pose proof (join_eq H H'); subst C end;
      repeat proof_irr; auto.
*     (* saf_assoc *)
      intros a b c d e H1 H2.
      destruct d as [rd | rd sd kd pd | kd pd].
      destruct a as [ra | | ]; try solve [elimtype False; inv H1].
      destruct b as [rb| | ]; try solve [elimtype False; inv H1].
      assert (join ra rb rd) by (inv H1; auto).
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO' _ rf (join_unreadable_shares H3 n1 n2)); split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf (join_readable2 H3 sc) kc pc).
      inv H2. split; constructor; auto.
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      destruct b as [ | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf (join_readable1 H3 sb) kd pd).  inv H1; inv H2; split; constructor; auto.
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO' _ rf (join_unreadable_shares H3 n0 n)).  inv H1; inv H2; split; constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf (join_readable1 H3 sb) kb pb).  inv H1; inv H2; split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf (join_readable2 H3 sc) kc pc).  inv H1; inv H2; split; constructor; auto.
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf (join_readable1 H3 sb) kb pb).  inv H1; inv H2; split; try constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf (join_readable1 H3 sb) kb pb).  inv H1; inv H2; split; try constructor; auto.
      exists (PURE' _ kd pd). inv H1; inv H2; split; constructor.

*      (* saf_com *)
      intros a b c H; inv H; econstructor;  apply join_comm; auto.

*     (* saf_positivity *)
     intros; inv H; inv H0; 
      repeat match goal with H: join ?A ?B ?C, H': join ?C ?D ?A |- _ => 
                    pose proof (join_positivity H H'); subst C 
      end; 
      repeat proof_irr; auto.
 Qed.

  Instance sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
  Proof. intros.
            apply mkSep 
             with (fun x => match x 
                             with NO' _ _ => NO' _ Share.bot bot_unreadable
                               | YES' _ _ _ _ => NO' _ Share.bot bot_unreadable
                               | PURE' k pds => PURE' _ k pds end).
            intro. destruct t; constructor; try apply join_unit1; auto.
            intros. inversion H; auto.
  Defined.

  Definition paf_res : @pafunctor f_res res_join.
  Proof. constructor; repeat intro.
  (* This is a little painful because of the way res_join is defined, but
      whatever... *)
   inv H; simpl; constructor; trivial.
   destruct z as [ rz | rz sz kz pz | kz pz ].
   destruct x' as [ rx' | rx' sx' kx' px' | kx' px' ]; try solve [elimtype False; inv H].
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   exists (NO' _ rx' n0); exists (NO' _ ry n1); inv H; split; constructor; tauto.
   destruct x' as [ rx' | rx' sx' kx' px' | kx' px' ]; try solve [elimtype False; inv H].
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   exists (NO' _ rx' n); exists (YES' _ ry sy kz pz); inv H; split; constructor; auto. simpl in *; f_equal; auto.
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   exists (YES' _ rx' sx' kx' pz); exists (NO' _ ry n); inv H; split; constructor; auto.
   exists (YES' _ rx' sx' kx' pz); exists (YES' _ ry sy ky pz); inv H; split; constructor; auto; simpl; f_equal; auto.
   exists (PURE' _ kz pz); exists (PURE' _ kz pz); simpl in *; inv H; split; [constructor | tauto].

   destruct x as [ rx | rx sx kx px | kx px ]; try solve [elimtype False; inv H].
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (NO' _ ry n0); exists (NO' _ rz n1); inv H; split; constructor; auto.
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (YES' _ ry sy ky py); exists (YES' _ rz sz ky py); inv H; split; constructor; auto.
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (NO' _ ry n); exists (YES' _ rz sz kx px); inv H; split; constructor; auto.
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (YES' _ ry sy kx px); exists (YES' _ rz sz kx px); inv H; split; constructor; auto. simpl; f_equal; auto.
   exists (PURE' _ kx px); exists (PURE' _ kx px); inv H; split; constructor; auto.
  Qed.

  Definition res_option (PRED : Type) (r: res PRED) : option (rshare * kind):=
    match r with
      | NO' _ _ => None
      | YES' sh rsh k _ => Some (readable_part rsh,k)
      | PURE' _ _ => None (* PUREs cannot be split in any interesting way, which is what valid is about. *)
    end.

  Inductive ghost (PRED : Type) : Type :=
    GHOST' I (RAs: I -> Ghost) (g: @G Global_Ghost) (pds: I -> nat -> option (fpreds PRED))
      (Hv: ghost.valid g)
      (dom: forall i n pp, pds i n = Some pp -> exists a, finmap_get (g i) n = Some a).

  Program Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    match x with
      | GHOST' _ RAs a pds _ _ =>
        GHOST' _ _ RAs a (fmap (ffunc (fconst _) (ffunc (fconst _) (foption fpreds))) f g pds) _ _
    end.
  Next Obligation.
  Proof.
    simpl in H.
    destruct (pds i n) eqn: Hi; inv H; eauto.
  Defined.

  Lemma ghost_ext: forall PRED I RAs g g' pds pds' Hv Hv' dom dom',
    g = g' -> pds = pds' -> GHOST' PRED I RAs g pds Hv dom = GHOST' PRED I RAs g' pds' Hv' dom'.
  Proof.
    intros; subst.
    f_equal; apply proof_irr.
  Qed.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
  Proof.
    constructor; intros; extensionality x; icase x; unfold ghost_fmap.
    - apply ghost_ext; auto.
      rewrite fmap_id; auto.
    - apply ghost_ext; auto.
      rewrite <- fmap_comp; auto.
  Qed.

  Definition f_ghost : functor := Functor ff_ghost.

  (* Will this give us the higher-order ghost state we want? *)
  Inductive ghost_join (PRED : Type) : f_ghost PRED -> f_ghost PRED -> f_ghost PRED -> Prop :=
    | ghost_join_I : forall A (RAs : A -> Ghost) a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc,
        join a b c -> join pdsa pdsb pdsc ->
        ghost_join PRED (GHOST' PRED _ RAs a pdsa Hva doma) (GHOST' PRED _ RAs b pdsb Hvb domb)
                        (GHOST' PRED _ RAs c pdsc Hvc domc).
  Lemma ghost_join_inv : forall PRED A RAs a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc,
    ghost_join PRED (GHOST' PRED A RAs a pdsa Hva doma) (GHOST' PRED A RAs b pdsb Hvb domb)
      (GHOST' PRED A RAs c pdsc Hvc domc) ->
      join a b c /\ join pdsa pdsb pdsc.
  Proof.
    inversion 1.
    repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
      subst); auto.
  Qed.

  Instance Join_ghost (PRED: Type) : Join (ghost PRED) := ghost_join PRED.

  Instance pa_gj : forall PRED, @Perm_alg _ (ghost_join PRED).
  Proof.
    constructor; intros.
    - inv H; inv H0.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst).
      apply ghost_ext; eapply join_eq; eauto.
    - destruct a as [I RA a pdsa], b as [I1 RA1 b pdsb], d as [I2 RA2 d pdsd].
      assert (I1 = I /\ I2 = I) as [] by (inv H; auto); subst.
      assert (RA1 = RA /\ RA2 = RA) as []; subst.
      { inv H.
        repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst); auto. }
      apply ghost_join_inv in H as [J1 J1'].
      destruct c as [I1 RA1 c pdsc], e as [I2 RA2 e pdse].
      assert (I1 = I /\ I2 = I) as [] by (inv H0; auto); subst.
      assert (RA1 = RA /\ RA2 = RA) as []; subst.
      { inv H0.
        repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst); auto. }
      apply ghost_join_inv in H0 as [J2 J2'].
      destruct (join_assoc J1 J2) as (f & ? & ?).
      destruct (join_assoc J1' J2') as (pdsf & ? & ?).
      assert (ghost.valid f) as Hvf by (eapply join_valid; eauto).
      assert (forall i n pp, pdsf i n = Some pp -> exists a, finmap_get (f i) n = Some a)
        as domf.
      { intros.
        specialize (H i); specialize (H1 i n).
        apply finmap_get_join with (i0 := n) in H.
        destruct (finmap_get (f i) n); eauto.
        inv H1.
        + rewrite H3 in H7; destruct (dom2 _ _ _ H7) as [? Hget].
          rewrite Hget in H.
          destruct (finmap_get (b i) n); inv H.
        + rewrite H3 in H7; destruct (dom0 _ _ _ H7) as [? Hget].
          rewrite Hget in H.
          destruct (finmap_get (c i) n); inv H.
        + symmetry in H4; destruct (dom0 _ _ _ H4) as [? Hget].
          rewrite Hget in H.
          destruct (finmap_get (c i) n); inv H. }
      exists (GHOST' PRED _ RA f pdsf Hvf domf); split; constructor; auto.
    - inv H; constructor; apply join_comm; auto.
    - inv H; inv H0.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
        subst); auto.
      apply ghost_ext; eapply join_positivity; eauto.
  Qed.

  Lemma core_dom: forall {PRED I} {RAs: I -> Ghost} (pds : I -> nat -> option (fpreds PRED))
    (g: @G Global_Ghost) i n pp, core pds i n = Some pp -> exists a, finmap_get (g i) n = Some a.
  Proof.
    discriminate.
  Qed.

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
  Proof.
    intros.
    exists (fun x => match x with GHOST' _ RA g pds Hv _ =>
                         GHOST' PRED _ RA (core g) (core pds) (core_valid _ Hv) (core_dom _ _) end).
    - destruct t; constructor; apply core_unit.
    - intros; inv H.
      apply ghost_ext; auto.
      eapply join_core; eauto.
  Defined.

  Definition paf_ghost : @pafunctor f_ghost ghost_join.
  Proof.
    constructor; repeat intro.
    - inv H; constructor; auto.
      intros i n; specialize (H1 i n); inv H1; simpl.
      + rewrite <- H2, H; constructor.
      + rewrite <- H3, H4; constructor.
      + inv H4.
        rewrite <- H, <- H2, <- H3; repeat constructor.
    - destruct x' as [I RA x pds], y as [I1 RA1 y pds1], z as [I2 RA2 z pds2].
      assert (I1 = I /\ I2 = I) as [] by (inv H; auto); subst.
      assert (RA1 = RA /\ RA2 = RA) as []; subst.
      { inv H.
        repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst; auto. }
      apply ghost_join_inv in H as [J J'].
      eexists (GHOST' A _ RA x (fun i n => match pds i n with Some _ => pds2 i n | _ => None end) Hv _),
        (GHOST' A _ RA y (fun i n => match pds1 i n with Some _ => pds2 i n | _ => None end) Hv0 _);
        repeat split; auto.
      + intros i n; specialize (J' i n); inv J'.
        * destruct (pds1 i n), (pds2 i n); inv H; constructor.
        * destruct (pds1 i n); inv H1.
          destruct (pds i n), (pds2 i n); inv H2; constructor.
        * destruct (pds1 i n); inv H0.
          destruct (pds2 i n); inv H1; constructor; auto.
      + apply ghost_ext; auto.
        extensionality i n; specialize (J' i n); inv J'; auto; simpl.
        * rewrite <- H0; auto.
        * rewrite H2.
          destruct (pds2 i n); auto.
        * rewrite <- H.
          destruct (pds1 i n); inv H0.
          destruct (pds2 i n); inv H1.
          inv H2; auto.
      + apply ghost_ext; auto; simpl.
        extensionality i n; specialize (J' i n); inv J'; auto.
        * destruct (pds1 i n), (pds2 i n); inv H; auto.
        * destruct (pds1 i n); inv H1; auto.
        * destruct (pds1 i n); inv H0.
          destruct (pds2 i n); inv H1.
          inv H2; auto.
    - destruct x as [I RA x pds], y as [I1 RA1 y pds1], z' as [I2 RA2 z pds2].
      assert (I1 = I /\ I2 = I) as [] by (inv H; auto); subst.
      assert (RA1 = RA /\ RA2 = RA) as []; subst.
      { inv H.
        repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst; auto. }
      apply ghost_join_inv in H as [J J'].
      eexists (GHOST' A _ RA y (fun i n => match pds i n, pds1 i n with Some x, Some _ => Some x
          | _, _ => pds1 i n end) Hv0 _),
        (GHOST' A _ RA z (fun i n => match pds i n with Some x => Some x | None => pds1 i n end) Hv1 _);
        repeat split; auto.
      + intros i n; specialize (J' i n); inv J'.
        * destruct (pds i n); inv H0; constructor.
        * destruct (pds1 i n); inv H1.
          destruct (pds i n); constructor.
        * destruct (pds i n); inv H.
          destruct (pds1 i n); inv H0; constructor; auto.
      + apply ghost_ext; auto; simpl.
        extensionality i n; specialize (J' i n); inv J'; auto.
        * destruct (pds i n); inv H0; constructor.
        * destruct (pds1 i n); inv H1.
          destruct (pds i n); constructor.
        * destruct (pds i n); inv H.
          destruct (pds1 i n); inv H0.
          inv H2; auto.
      + apply ghost_ext; auto; simpl.
        extensionality i n; specialize (J' i n); inv J'; auto.
        * destruct (pds i n); inv H0; constructor.
        * destruct (pds1 i n); inv H1.
          destruct (pds i n); constructor.
        * destruct (pds i n); inv H.
          destruct (pds1 i n); inv H0.
          inv H2; auto.
    Unshelve.
    simpl; intros; destruct (pds i n) eqn: Hi; inv H; eauto.
    simpl; intros; destruct (pds1 i n) eqn: Hi; inv H; eauto.
    simpl; intros; destruct (pds i n) eqn: Hi, (pds1 i n) eqn: Hi1; inv H; eauto.
    simpl; intros.
    specialize (J i); specialize (J' i n); apply finmap_get_join with (i0 := n) in J.
    destruct (finmap_get (z i) n); eauto.
    inv J'.
    destruct (pds i n); inv H1.
    destruct (dom0 _ _ _ H) as [? Hget]; rewrite Hget in J.
    destruct (finmap_get (x i) n); inv J.
    destruct (pds1 i n); inv H2.
    destruct (pds i n) eqn: Hi; inv H.
    destruct (dom _ _ _ Hi) as [? Hget]; rewrite Hget in J.
    destruct (finmap_get (y i) n); inv J.
    destruct (pds i n) eqn: Hi; inv H0.
    destruct (dom _ _ _ Hi) as [? Hget]; rewrite Hget in J.
    destruct (finmap_get (y i) n); inv J.
  Qed.

  Definition valid' A (w: (address -> res A) * ghost A) : Prop :=
    AV.valid (fun l => res_option A (fst w l)).

  Lemma same_valid : forall f1 f2, (forall x, f1 x = f2 x) -> AV.valid f1 -> AV.valid f2.
  Proof.
    intros; replace f2 with f1; trivial.
    apply extensionality; auto.
  Qed.

  Lemma valid'_res_map : forall A B f g m,
    valid' A m -> valid' B (fmap f_res f g oo fst m, fmap f_ghost f g (snd m)).
  Proof.
    unfold valid'; intros A B f g m.
    apply same_valid; intro l.
    unfold compose; simpl.
    destruct (fst m l); simpl; auto.
  Qed.

  Lemma valid'_res_map2 : forall A B f g m,
    valid' B (fmap f_res f g oo fst m, fmap f_ghost f g (snd m)) -> valid' A m.
  Proof.
    unfold valid'; intros A B f g m.
    apply same_valid; intro l.
    unfold compose; simpl.
    destruct (fst m l) eqn: Hl; setoid_rewrite Hl; auto.
  Qed.

  Definition pre_rmap (A:Type) := { m:(address -> res A) * ghost A | valid' A m }.
  Definition f_pre_rmap : functor :=
    fsubset (fpair (ffunc (fconst address) f_res) f_ghost) _ valid'_res_map.

  Notation Join_obj A := (Join_prod _ (Join_fun address (res A) (res_join A)) _ (Join_ghost A)).

  Instance Join_pre_rmap (A: Type) : Join (pre_rmap A) :=
    Join_prop _ (Join_obj A) (valid' A).

  Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap :=
    paf_subset (paf_pair (paf_fun address paf_res) paf_ghost) valid' valid'_res_map valid'_res_map2.

  Lemma pre_rmap_sa_valid_core (A: Type):
        forall x,
       valid' A x ->
       valid' A  (@core ((address -> res A) * ghost A) (Join_obj A)
         (Sep_prod (Sep_fun address (res A) (res_join A) (sa_rj A)) (sa_gj A)) x).
  Proof.
    intros. red. red.
    replace (fun l => res_option A (fst (core x) l)) with (fun l : address => @None (rshare * kind)).
    apply AV.valid_empty.
    extensionality a. simpl. icase (fst x a).
  Qed.


  Lemma pre_rmap_sa_valid_join : forall A (x y z : (address -> res A) * ghost A),
    @join _ (Join_obj A) x y z ->
    valid' A x -> valid' A y -> valid' A z.
  Proof.
     intros.
     simpl in H.
     unfold valid' in *.
     apply AV.valid_join with (fun l => res_option A (fst x l)) (fun l => res_option A (fst y l)); auto.
     intro l. inv H.
     spec H2 l. inv H2; try constructor; simpl.
     - apply join_comm in H6.
       rewrite (join_readable_part_eq rsh2 nsh1 rsh3 H6). constructor.
     - rewrite (join_readable_part_eq rsh1 nsh2 rsh3 H6). constructor.
     - constructor.
       red. red. simpl.
       clear - H6. destruct H6. split.
       + rewrite Share.glb_assoc. rewrite <- (Share.glb_assoc sh1).
         rewrite (Share.glb_commute sh1). rewrite Share.glb_assoc.
         rewrite <- (Share.glb_assoc Share.Rsh).
         rewrite H. rewrite Share.glb_bot. auto.
       + rewrite <- Share.distrib1. rewrite H0. auto.
       + constructor. reflexivity. reflexivity.
  Qed.

  Definition Perm_pre_rmap (A: Type): Perm_alg (pre_rmap A) :=
    Perm_prop _ _ (Perm_prod (Perm_fun address _ _ _) (pa_gj A)) _ (pre_rmap_sa_valid_join _).

  Instance Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A) :=
    Sep_prop _ _ (Perm_prod (Perm_fun address _ _ _) (pa_gj A)) _ (pre_rmap_sa_valid_join _)  _ (pre_rmap_sa_valid_core _).

  Lemma pre_rmap_core: forall A (m : f_pre_rmap A),
    exists P, core m = exist (valid' A) (core (proj1_sig m)) P.
  Proof.
    simpl; eauto.
  Qed.

End StratModel.

Local Open Scope nat_scope.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.
  Import AV.

  Parameter rmap : Type.
  Axiom Join_rmap: Join rmap. Existing Instance Join_rmap.
  Axiom Perm_rmap: Perm_alg rmap. Existing Instance Perm_rmap.
  Axiom Sep_rmap: Sep_alg rmap. Existing Instance Sep_rmap.
  Axiom ag_rmap: ageable rmap.  Existing Instance ag_rmap.
  Axiom Age_rmap: Age_alg rmap.  Existing Instance Age_rmap.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
      (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~(readable_share sh) -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.

  Definition res_option (r:resource) : option (rshare * kind) :=
    match r with
      | NO _ _ => None
      | YES sh rsh k _ => Some (readable_part rsh,k)
      | PURE k _ => None
    end.

  Inductive res_join : resource -> resource -> resource -> Prop :=
   | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (NO sh2 nsh2) (NO sh3 nsh3)
   | res_join_NO2 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3), 
                 res_join (YES sh1 rsh1 k p) (NO sh2 nsh2) (YES sh3 rsh3 k p) 
   | res_join_NO3 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p) 
   | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
        res_join (YES sh1 rsh1 k p) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
   | res_join_PURE : forall k p, res_join (PURE k p) (PURE k p) (PURE k p). 

  Instance Join_resource: Join resource := res_join.
  Axiom Perm_resource: Perm_alg resource. Existing Instance Perm_resource.
  Axiom Sep_resource: Sep_alg resource. Existing Instance Sep_resource.

  Definition preds_fmap (f g: pred rmap -> pred rmap) (x:preds) : preds :=
    match x with SomeP A Q => SomeP A (fmap (fpi _) f g Q)
    end.
  (* Check whether the following two can be erased. *)
  Axiom preds_fmap_id : preds_fmap (id _) (id _) = id preds.
  Axiom preds_fmap_comp : forall f1 f2 g1 g2,
    preds_fmap g1 g2 oo preds_fmap f1 f2 = preds_fmap (g1 oo f1) (f2 oo g2).

  Instance preds_join (I: Type) : Join (I -> nat -> option preds) :=
    Join_fun _ _ (Join_fun _ _ (Join_lower (Join_equiv preds))).

  Definition resource_fmap (f g:pred rmap -> pred rmap) (x:resource) : resource :=
    match x with
    | NO sh nsh => NO sh nsh
    | YES sh rsh k p => YES sh rsh k (preds_fmap f g p)
    | PURE k p => PURE k (preds_fmap f g p)
    end.
  Axiom resource_fmap_id : resource_fmap (id _) (id _) = id resource.
  Axiom resource_fmap_comp : forall f1 f2 g1 g2,
    resource_fmap g1 g2 oo resource_fmap f1 f2 = resource_fmap (g1 oo f1) (f2 oo g2).

  Inductive ghost : Type := GHOST I (RA : I -> Ghost) (g : @G Global_Ghost) (pds : I -> nat -> option preds)
    (Hv : ghost.valid g)
    (dom : forall i n pp, pds i n = Some pp -> exists a, finmap_get (g i) n = Some a).

  Lemma ghost_ext: forall I RAs g g' pds pds' Hv Hv' dom dom',
    g = g' -> pds = pds' -> GHOST I RAs g pds Hv dom = GHOST I RAs g' pds' Hv' dom'.
  Proof.
    intros; subst.
    f_equal; apply proof_irr.
  Qed.

  (* Will this give us the higher-order ghost state we want? *)
  Inductive ghost_join : ghost -> ghost -> ghost -> Prop :=
    | ghost_join_I : forall A (RA : A -> Ghost) a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc, join a b c ->
        join pdsa pdsb pdsc ->
        ghost_join (GHOST _ RA a pdsa Hva doma) (GHOST _ RA b pdsb Hvb domb) (GHOST _ RA c pdsc Hvc domc).
  Lemma ghost_join_inv : forall A RAs a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc,
    ghost_join (GHOST A RAs a pdsa Hva doma) (GHOST A RAs b pdsb Hvb domb) (GHOST A RAs c pdsc Hvc domc) ->
    join a b c /\ join pdsa pdsb pdsc.
  Proof.
    inversion 1.
    repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
      subst); auto.
  Qed.

  Lemma core_dom: forall {I} {RAs: I -> Ghost} (pds : I -> nat -> option preds)
    (g: @G Global_Ghost) i n pp, core pds i n = Some pp -> exists a, finmap_get (g i) n = Some a.
  Proof.
    discriminate.
  Qed.

  Instance Join_ghost : Join ghost := ghost_join.
  Axiom Perm_ghost: Perm_alg ghost. Existing Instance Perm_ghost.
  Axiom Sep_ghost: Sep_alg ghost. Existing Instance Sep_ghost.
  Axiom ghost_core: forall A (RA : A -> Ghost) a pds Hv dom,
    core (GHOST _ RA a pds Hv dom) = GHOST _ RA (core a) (core pds) (core_valid _ Hv) (core_dom _ _).

  Program Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    match x with
      | GHOST _ RA a pds _ _ => GHOST _ RA a (fun i n => option_map (preds_fmap f g) (pds i n)) _ _
    end.
  Next Obligation.
  Proof.
    simpl in H.
    destruct (pds i n) eqn: Hi; inv H; eauto.
  Defined.

  Axiom ghost_fmap_id : ghost_fmap (id _) (id _) = id ghost.
  Axiom ghost_fmap_comp : forall f1 f2 g1 g2,
    ghost_fmap g1 g2 oo ghost_fmap f1 f2 = ghost_fmap (g1 oo f1) (f2 oo g2).

  Definition valid (m: (address -> resource) * ghost) : Prop :=
    AV.valid  (res_option oo fst m).

  Axiom valid_res_map : forall f g m, valid m -> valid (resource_fmap f g oo fst m, ghost_fmap f g (snd m)).
  Axiom rmapj_valid_join : forall (x y z : (address -> resource) * ghost),
    join x y z -> valid x -> valid y -> valid z.
  Axiom rmapj_valid_core: forall x: (address -> resource) * ghost, valid x -> valid (core x).

  Definition rmap' := sig valid.

  Definition rmap_fmap (f g: pred rmap -> pred rmap) (x:rmap') : rmap' :=
    match x with exist m H => exist (fun m => valid m) (resource_fmap f g oo fst m, ghost_fmap f g (snd m)) (valid_res_map f g m H) end.
  Axiom rmap_fmap_id : rmap_fmap (id _) (id _) = id rmap'.
  Axiom rmap_fmap_comp : forall f1 f2 g1 g2,
   rmap_fmap g1 g2 oo rmap_fmap f1 f2 = rmap_fmap (g1 oo f1) (f2 oo g2).

  Parameter squash : (nat * rmap') -> rmap.
  Parameter unsquash : rmap -> (nat * rmap').


  Axiom rmap_level_eq: @level rmap _ = fun x => fst (unsquash x).
  Axiom rmap_age1_eq: @age1 _ _ =
     fun k => match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Definition resource_at (phi:rmap) : address -> resource := fst (proj1_sig (snd (unsquash phi))).
  Infix "@" := resource_at (at level 50, no associativity).
  Definition ghost_of (phi:rmap) : ghost := snd (proj1_sig (snd (unsquash phi))).

  Instance Join_nat_rmap': Join (nat * rmap') := Join_prod _ (Join_equiv nat) _ _.

  Axiom join_unsquash : forall phi1 phi2 phi3,
    join phi1 phi2 phi3 <->
    join (unsquash phi1) (unsquash phi2) (unsquash phi3).

  Definition rmap_unage (k:rmap) : rmap :=
    match unsquash k with
    | (n,x) => squash (S n, x)
    end.

  Program Definition approx (n:nat) (p: pred rmap) : pred rmap :=
    fun w => level w < n /\ p w.
  Next Obligation.
  destruct H0.
  split.
  apply age_level in H. omega.
  apply pred_hereditary with a; auto.
  Qed.

  Axiom squash_unsquash : forall phi, squash (unsquash phi) = phi.
  Axiom unsquash_squash : forall n rm, unsquash (squash (n,rm)) = (n,rmap_fmap (approx n) (approx n) rm).
  Axiom ghost_of_core : forall phi, ghost_of (core phi) = core (ghost_of phi).

End RMAPS.

Module Rmaps (AV':ADR_VAL): RMAPS with Module AV:=AV'.
  Module AV:=AV'.
  Import AV.

  Module SM := StratModel(AV).
  Import SM.

  Module TyF. (* <: TY_FUNCTOR_PROP. *)
    Definition F := f_pre_rmap.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.
    Import KI.

    Instance Join_F: forall A, Join (F A) := _.
    Definition Perm_F : forall A, Perm_alg (F A) := Perm_pre_rmap.
    Definition Sep_F := Sep_pre_rmap.
    Definition paf_F := paf_pre_rmap.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).
  Module KL := KnotLemmas_MixVariantHeredProp(K).
  Module KSa := KnotFullSa(TyFSA)(K)(KL).

  Definition rmap := K.knot.
  Instance Join_rmap: Join rmap := KSa.Join_knot.
  Instance Perm_rmap : Perm_alg rmap:= KSa.Perm_knot.
  Instance Sep_rmap : Sep_alg rmap:= KSa.Sep_knot.
  Instance ag_rmap : ageable rmap := K.ageable_knot.
  Instance Age_rmap: Age_alg rmap := KSa.asa_knot.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
    (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~ readable_share sh -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.

  Definition resource2res (r: resource): res (pred rmap) :=
    match r with
      | NO sh nsh => NO' (pred rmap) sh nsh
      | YES sh rsh k (SomeP A l) => YES' (pred rmap) sh rsh k (existT _ A l)
      | PURE k (SomeP A l) => PURE' (pred rmap) k (existT _ A l)
    end.

  Definition res2resource (r: res (pred rmap)) : resource :=
    match r with
      | NO' sh nsh => NO sh nsh
      | YES' sh rsh k (existT A l) => YES sh rsh k (SomeP A l)
      | PURE' k (existT A l) => PURE k (SomeP A l)
    end.

  Lemma res2resource2res: forall x, resource2res (res2resource x) = x.
  Proof. unfold resource2res, res2resource; destruct x as [? | ? ? ? [? ?] | ? [? ?]]; auto. Qed.

  Lemma resource2res2resource: forall x, res2resource (resource2res x) = x.
  Proof. unfold resource2res, res2resource; destruct x; try destruct p0; try destruct p; auto. Qed.

  Definition res_option (r:resource) : option (rshare * kind) :=
    match r with
      | NO _ _ => None
      | YES sh rsh k _ => Some (readable_part rsh,k)
      | PURE k _ => None
    end.

  Lemma res_option_rewrite: res_option = SM.res_option (pred rmap) oo resource2res.
  Proof.
    unfold SM.res_option, res_option, compose.
    extensionality r; destruct r; simpl; auto; destruct p; auto.
  Qed.

  Inductive ghost : Type := GHOST I (RAs : I -> Ghost) (g : @G Global_Ghost) (pds : I -> nat -> option preds)
    (Hv : ghost.valid g)
    (dom : forall i n pp, pds i n = Some pp -> exists a, finmap_get (g i) n = Some a).

  Definition pred2p (p: preds) : fpreds (pred rmap) :=
    match p with SomeP A P => existT _ A P end.

  Definition p2pred (p: fpreds (pred rmap)) : preds :=
    match p with existT A P => SomeP A P end.

  Program Definition ghost2g (r: ghost): SM.ghost (pred rmap) :=
    match r with
      | GHOST _ RA g pds _ _ => GHOST' (pred rmap) _ RA g (fun i n => option_map pred2p (pds i n)) _ _
    end.
  Next Obligation.
  Proof.
    destruct (pds i n) eqn: Hi; inv H; eauto.
  Defined.

  Program Definition g2ghost (r: SM.ghost (pred rmap)) : ghost :=
    match r with
      | GHOST' _ RA g pds _ _ => GHOST _ RA g (fun i n => option_map p2pred (pds i n)) _ _
    end.
  Next Obligation.
  Proof.
    destruct (pds i n) eqn: Hi; inv H; eauto.
  Defined.

  Lemma ghost_ext: forall I RAs g g' pds pds' Hv Hv' dom dom',
    g = g' -> pds = pds' -> GHOST I RAs g pds Hv dom = GHOST I RAs g' pds' Hv' dom'.
  Proof.
    intros; subst.
    f_equal; apply proof_irr.
  Qed.

  Lemma g2ghost2g: forall x, ghost2g (g2ghost x) = x.
  Proof.
    destruct x; apply SM.ghost_ext; auto.
    extensionality i n; destruct (pds i n) as [[]|]; auto.
  Qed.

  Lemma ghost2g2ghost: forall x, g2ghost (ghost2g x) = x.
  Proof.
    destruct x; apply ghost_ext; auto.
    extensionality i n; destruct (pds i n) as [[]|]; auto.
  Qed.

  Definition valid (m: (address -> resource) * ghost) : Prop :=
    AV.valid  (res_option oo fst m).

  Inductive res_join : resource -> resource -> resource -> Prop :=
   | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (NO sh2 nsh2) (NO sh3 nsh3)
   | res_join_NO2 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3), 
                 res_join (YES sh1 rsh1 k p) (NO sh2 nsh2) (YES sh3 rsh3 k p) 
   | res_join_NO3 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p) 
   | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
        res_join (YES sh1 rsh1 k p) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
   | res_join_PURE : forall k p, res_join (PURE k p) (PURE k p) (PURE k p).

  Instance Join_resource: Join resource := res_join.
  Instance Perm_resource: Perm_alg resource.
  Proof. constructor.
  * (*saf_eq *)
      intros x y z z' H1 H2; inv H1; inv H2;
      repeat match goal with H: join ?A ?B _, H': join ?A ?B ?C |- _ => pose proof (join_eq H H'); subst C end;
      repeat proof_irr; auto.
  * (* saf_assoc *)
      intros a b c d e H1 H2.
      destruct d as [rd | rd sd kd pd | kd pd].
      destruct a as [ra | | ]; try solve [elimtype False; inv H1].
      destruct b as [rb| | ]; try solve [elimtype False; inv H1].
      assert (join ra rb rd) by (inv H1; auto).
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO rf (join_unreadable_shares H3 n1 n2)); split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf (join_readable2 H3 sc) kc pc).
      inv H2. split; constructor; auto.
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      destruct b as [ | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf (join_readable1 H3 sb) kd pd).  inv H1; inv H2; split; constructor; auto.
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO rf (join_unreadable_shares H3 n0 n)).  inv H1; inv H2; split; constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf (join_readable1 H3 sb) kb pb).  inv H1; inv H2; split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf (join_readable2 H3 sc) kc pc).  inv H1; inv H2; split; constructor; auto.
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf (join_readable1 H3 sb) kb pb).  inv H1; inv H2; split; try constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf (join_readable1 H3 sb) kb pb).  inv H1; inv H2; split; try constructor; auto.
      exists (PURE kd pd). inv H1; inv H2; split; constructor.

*      (* saf_com *)
      intros a b c H; inv H; econstructor;  apply join_comm; auto.

*     (* saf_positivity *)
     intros; inv H; inv H0; 
      repeat match goal with H: join ?A ?B ?C, H': join ?C ?D ?A |- _ => 
                    pose proof (join_positivity H H'); subst C 
      end; 
      repeat proof_irr; auto.
 Qed.

  Instance Sep_resource: Sep_alg resource.
  Proof.
  apply mkSep 
    with (fun x => match x 
                   with NO _ _ => NO Share.bot bot_unreadable
                      | YES _ _ _ _ => NO Share.bot bot_unreadable
                      | PURE k pds => PURE k pds end).
  intro. destruct t; constructor; try apply join_unit1; auto.
  intros. inversion H; auto.
  Defined.

  Instance preds_join (I: Type) : Join (I -> nat -> option preds) :=
    Join_fun _ _ (Join_fun _ _ (Join_lower (Join_equiv preds))).

  (* Will this give us the higher-order ghost state we want? *)
  Inductive ghost_join : ghost -> ghost -> ghost -> Prop :=
    | ghost_join_I : forall A (RA : A -> Ghost) a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc, join a b c ->
        join pdsa pdsb pdsc ->
        ghost_join (GHOST _ RA a pdsa Hva doma) (GHOST _ RA b pdsb Hvb domb) (GHOST _ RA c pdsc Hvc domc).

  Lemma ghost_join_inv : forall A RAs a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc,
    ghost_join (GHOST A RAs a pdsa Hva doma) (GHOST A RAs b pdsb Hvb domb) (GHOST A RAs c pdsc Hvc domc) ->
    join a b c /\ join pdsa pdsb pdsc.
  Proof.
    inversion 1.
    repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
      subst); auto.
  Qed.

  Instance Join_ghost : Join ghost := ghost_join.

  Instance Perm_ghost : Perm_alg ghost.
  Proof.
    constructor; intros.
    - inv H; inv H0.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst).
      apply ghost_ext; eapply join_eq; eauto.
    - destruct a as [I RA a pdsa], b as [I1 RA1 b pdsb], d as [I2 RA2 d pdsd].
      assert (I1 = I /\ I2 = I) as [] by (inv H; auto); subst.
      assert (RA1 = RA /\ RA2 = RA) as []; subst.
      { inv H.
        repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst); auto. }
      apply ghost_join_inv in H as [J1 J1'].
      destruct c as [I1 RA1 c pdsc], e as [I2 RA2 e pdse].
      assert (I1 = I /\ I2 = I) as [] by (inv H0; auto); subst.
      assert (RA1 = RA /\ RA2 = RA) as []; subst.
      { inv H0.
        repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst); auto. }
      apply ghost_join_inv in H0 as [J2 J2'].
      destruct (join_assoc J1 J2) as (f & ? & ?).
      destruct (join_assoc J1' J2') as (pdsf & ? & ?).
      assert (ghost.valid f) as Hvf by (eapply join_valid; eauto).
      assert (forall i n pp, pdsf i n = Some pp -> exists a, finmap_get (f i) n = Some a)
        as domf.
      { intros.
        specialize (H i); specialize (H1 i n).
        apply finmap_get_join with (i0 := n) in H.
        destruct (finmap_get (f i) n); eauto.
        inv H1.
        + rewrite H3 in H7; destruct (dom2 _ _ _ H7) as [? Hget].
          rewrite Hget in H.
          destruct (finmap_get (b i) n); inv H.
        + rewrite H3 in H7; destruct (dom0 _ _ _ H7) as [? Hget].
          rewrite Hget in H.
          destruct (finmap_get (c i) n); inv H.
        + symmetry in H4; destruct (dom0 _ _ _ H4) as [? Hget].
          rewrite Hget in H.
          destruct (finmap_get (c i) n); inv H. }
      exists (GHOST _ RA f pdsf Hvf domf); split; constructor; auto.
    - inv H; constructor; apply join_comm; auto.
    - inv H; inv H0.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
        subst); auto.
      apply ghost_ext; eapply join_positivity; eauto.
  Qed.

  Lemma core_dom: forall {I} {RAs: I -> Ghost} (pds : I -> nat -> option preds)
    (g: @G Global_Ghost) i n pp, core pds i n = Some pp -> exists a, finmap_get (g i) n = Some a.
  Proof.
    discriminate.
  Qed.

  Instance Sep_ghost : Sep_alg ghost.
  Proof.
    intros.
    exists (fun x => match x with GHOST _ RA g pds Hv _ => GHOST _ RA (core g) (core pds) (core_valid _ Hv) (core_dom _ _) end).
    - destruct t; constructor; apply core_unit.
    - intros; inv H.
      apply ghost_ext; auto.
      eapply join_core; eauto.
  Defined.

  Lemma ghost_core : forall A (RA : A -> Ghost) a pds Hv dom,
    core (GHOST _ RA a pds Hv dom) = GHOST _ RA (core a) (core pds) (core_valid _ Hv) (core_dom _ _).
  Proof. auto. Qed.

  Lemma same_valid : forall f1 f2, (forall x, f1 x = f2 x) -> AV.valid f1 -> AV.valid f2.
  Proof.
    intros; replace f2 with f1; trivial.
    apply extensionality; auto.
  Qed.

  Lemma rmapj_valid_core: forall x : (address -> resource) * ghost, valid x -> valid (core x).
  Proof.
     unfold valid, compose; intros. red. red. 
     replace (fun x0 => res_option (fst (core x) x0)) with (fun _ : address => @None (rshare * kind)).

     apply AV.valid_empty.
     extensionality a. simpl. icase (fst x a).
  Qed.

  Lemma rmapj_valid_join : forall (x y z : (address -> resource) * ghost),
    join x y z ->
    valid x -> valid y -> valid z.
  Proof.
     intros.
     simpl in H.
     unfold valid, compose in *.
     apply AV.valid_join with (fun l => res_option (fst x l)) (fun l => res_option (fst y l)); auto.
     intro l. inv H. specialize (H2 l). inv H2; eauto.
     - constructor.
     - simpl.
       rewrite (join_readable_part_eq rsh1 nsh2 rsh3 RJ). constructor.
     - apply join_comm in RJ.
       simpl.
       rewrite (join_readable_part_eq rsh2 nsh1 rsh3 RJ). constructor.
     - constructor. constructor.
       + simpl. red. red. simpl.
         clear - RJ. destruct RJ. split.
         * rewrite Share.glb_assoc. rewrite <- (Share.glb_assoc sh1).
           rewrite (Share.glb_commute sh1). rewrite Share.glb_assoc.
           rewrite <- (Share.glb_assoc Share.Rsh).
           rewrite H. rewrite Share.glb_bot. auto.
         * rewrite <- Share.distrib1. rewrite H0. auto.
       + constructor; reflexivity.
    - constructor.
  Qed.

  Definition rmap' := sig valid.
  Definition preds_fmap (f g:(pred rmap)->(pred rmap)) (x:preds) : preds :=
    match x with SomeP A ls => SomeP A (fmap (fpi _) f g ls) end.

  Lemma preds_fmap_id : preds_fmap (id (pred rmap)) (id (pred rmap)) = id preds.
  Proof.
    intros; apply extensionality; intro x; destruct x; simpl; auto.
    unfold id at 3.
    f_equal.
    extensionality i.
    rewrite fmap_id; auto.
  Qed.

  Lemma preds_fmap_comp : forall f1 f2 g1 g2,
    preds_fmap g1 g2 oo preds_fmap f1 f2 = preds_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros; apply extensionality; intro x; destruct x; simpl.
    unfold preds_fmap, compose at 1; simpl.
    f_equal.
    extensionality i.
    rewrite <- fmap_comp; auto.
  Qed.

  Definition resource_fmap (f g:pred rmap -> pred rmap) (x:resource) : resource :=
    match x with
    | NO sh nsh => NO sh nsh
    | YES sh rsh k p => YES sh rsh k (preds_fmap f g p)
    | PURE k p => PURE k (preds_fmap f g p)
    end.

  Program Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    match x with
      | GHOST _ RA a pds _ _ => GHOST _ RA a (fun i n => option_map (preds_fmap f g) (pds i n)) _ _
    end.
  Next Obligation.
  Proof.
    simpl in H.
    destruct (pds i n) eqn: Hi; inv H; eauto.
  Defined.

  Lemma valid_res_map : forall f g m, valid m -> valid (resource_fmap f g oo fst m, ghost_fmap f g (snd m)).
  Proof.
    unfold valid, compose; intros; simpl.
    replace (fun l : address => res_option (resource_fmap f g (fst m l)))
       with (fun l : address => res_option (fst m l)); auto.
    extensionality l.
    unfold res_option, resource_fmap.
    case (fst m l); auto.
  Qed.

  Lemma resource_fmap_id :
    resource_fmap (id (pred rmap)) (id (pred rmap)) = id resource.
  Proof.
    intros; apply extensionality; intro x.
    unfold resource_fmap.
    destruct x; simpl; auto.
    rewrite preds_fmap_id; auto.
    rewrite preds_fmap_id; auto.
  Qed.

  Lemma ghost_fmap_id : ghost_fmap (id (pred rmap)) (id (pred rmap)) = id ghost.
  Proof.
    extensionality x; destruct x; apply ghost_ext; auto.
    rewrite preds_fmap_id; unfold id; f_equal.
    extensionality i n.
    destruct (pds i n); auto.
  Qed.

  Lemma resource_fmap_comp : forall f1 f2 g1 g2,
    resource_fmap g1 g2 oo resource_fmap f1 f2 = resource_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros f1 f2 g1 g2.
    apply extensionality; intro x; destruct x; simpl; auto.
    unfold compose at 1; simpl.
    rewrite <- preds_fmap_comp; auto.
    rewrite <- preds_fmap_comp; auto.
  Qed.

  Lemma ghost_fmap_comp : forall f1 f2 g1 g2,
    ghost_fmap g1 g2 oo ghost_fmap f1 f2 = ghost_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros; extensionality x; destruct x; apply ghost_ext; auto.
    extensionality i n.
    destruct (pds i n); auto; simpl.
    rewrite <- preds_fmap_comp; auto.
  Qed.

  Definition rmap_fmap (f g:(pred rmap)->(pred rmap)) (x:rmap') : rmap' :=
    match x with exist m H => exist (fun m => valid m) _ (valid_res_map f g m H) end.

  Lemma rmap_fmap_id : rmap_fmap (id (pred rmap)) (id (pred rmap)) = id rmap'.
  Proof.
    intros; apply extensionality; intro x.
    unfold rmap_fmap; destruct x.
    unfold id at 7.
    generalize (valid_res_map (id _) (id _) x v).
    rewrite resource_fmap_id, ghost_fmap_id.
    rewrite (id_unit2 _ (resource) (fst x)).
    intro v0. destruct x; simpl. f_equal; auto. apply proof_irr.
  Qed.

  Lemma rmap_fmap_comp : forall f1 f2 g1 g2,
    rmap_fmap g1 g2 oo rmap_fmap f1 f2 = rmap_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros f1 f2 g1 g2.
    unfold rmap_fmap.
    apply extensionality; intro x.
    unfold compose at 1.
    destruct x.
    generalize (valid_res_map g1 g2 (resource_fmap f1 f2 oo fst x, ghost_fmap f1 f2 (snd x)) (valid_res_map f1 f2 x v)).
    generalize (valid_res_map (g1 oo f1) (f2 oo g2) x v).
    clear.
    assert (resource_fmap g1 g2 oo resource_fmap f1 f2 oo fst x = resource_fmap (g1 oo f1) (f2 oo g2) oo fst x).
    { rewrite <- compose_assoc.
      rewrite resource_fmap_comp; auto. }
    simpl; rewrite H.
    pose proof ghost_fmap_comp as HG.
    unfold compose in HG at 1; rewrite <- HG.
    intros.
    f_equal; proof_irr; auto.
  Qed.

  Definition rmap'2pre_rmap (r: rmap') : f_pre_rmap (pred rmap).
    destruct r as [f ?].
    unfold f_pre_rmap.
    assert (valid' _ (fun x: address => resource2res (fst f x), ghost2g (snd f))).
    unfold valid'. unfold valid, compose in v.
    eapply same_valid; try apply v.
    intros. simpl.
    destruct (fst f x); simpl; auto; destruct p; simpl; auto.
    eexists. exact H.
  Defined.

  Definition pre_rmap2rmap' (r: f_pre_rmap (pred rmap)) : rmap'.
    destruct r as [f ?].
    unfold rmap', valid' in *.
    assert (valid (fun l: address => res2resource (fst f l), g2ghost (snd f))).
    unfold valid, compose.
    simpl.
    assert ((fun l : address => res_option (res2resource (fst f l))) = (fun l : address => SM.res_option (pred rmap) (fst f l))).
    { extensionality l. rewrite res_option_rewrite.
      unfold compose; simpl. rewrite res2resource2res. auto. }
    setoid_rewrite H; auto.
    eauto.
  Defined.

  Lemma rmap'2pre_rmap2rmap' :
    forall x, rmap'2pre_rmap (pre_rmap2rmap' x) = x.
  Proof.
    intro. destruct x as [f V]. unfold rmap'2pre_rmap, pre_rmap2rmap'. simpl.
    match goal with |- exist _ _ ?p = _ => generalize p; intro p1 end.
    apply exist_ext.
    destruct f; simpl; f_equal.
    extensionality x; rewrite res2resource2res; auto.
    rewrite g2ghost2g; auto.
  Qed.

  Lemma pre_rmap2rmap'2pre_rmap :
    forall x,  pre_rmap2rmap' (rmap'2pre_rmap x) = x.
  Proof.
    intro.
    destruct x as [f V].
    unfold rmap'2pre_rmap, pre_rmap2rmap'. simpl.
    match goal with |- exist _ _ ?p = _ => generalize p; intro p1 end.
    apply exist_ext.
    destruct f; simpl; f_equal.
    extensionality x; rewrite resource2res2resource; auto.
    rewrite ghost2g2ghost; auto.
  Qed.
(*
  Program Definition p2p (p:(pred rmap)) : K.predicate :=
    fun phi_e => p phi_e.
  Next Obligation.
    unfold age, age1 in H. simpl in H. simpl in *.
    eapply pred_hereditary; eauto.
 Qed.

  Program Definition p2p' (p:K.predicate) : (pred rmap) :=
    fun (v:rmap) => p v.
  Next Obligation.
  unfold age in H; simpl in H.
  unfold rmap in *.
  eapply pred_hereditary; eauto.
 Qed.
*)
  Definition squash (n_rm:nat * rmap') : rmap :=
    match n_rm with (n,rm) => K.squash (n, rmap'2pre_rmap rm) end.

  Definition unsquash (phi:rmap) : (nat * rmap') :=
    match K.unsquash phi with (n,rm) => (n, pre_rmap2rmap' rm) end.

  Definition rmap_level (phi:rmap) : nat := fst (unsquash phi).
  Definition resource_at (phi:rmap) : address -> resource := fst (proj1_sig (snd (unsquash phi))).
  Infix "@" := resource_at (at level 50, no associativity).
  Definition ghost_of (phi:rmap) : ghost := snd (proj1_sig (snd (unsquash phi))).

  Lemma pred_ext': forall {A} `{agA: ageable A} P Q,
                (forall x, app_pred P x <-> app_pred Q x) -> P = Q.
  Proof. intros; apply pred_ext; intro; apply H; auto. Qed.

  Lemma squash_unsquash : forall phi, squash (unsquash phi) = phi.
  Proof.
    intros.
    unfold squash, unsquash; simpl.
    destruct (K.unsquash phi) eqn:?H; simpl; intros.
    rewrite rmap'2pre_rmap2rmap'.
    unfold K.KI.F in *.
    unfold f_pre_rmap in H.
    match goal with
    | |- K.squash ?A = _ => replace A with (K.unsquash phi)
    end.
    rewrite K.squash_unsquash; auto.
  Qed.

  Program Definition approx (n:nat) (p: (pred rmap)) : (pred rmap) :=
    fun w => level w < n /\ p w.
  Next Obligation.
  destruct H0.
  split.
  apply age_level in H.
  simpl in *. omega.
  apply pred_hereditary with a; auto.
  Qed.

  Lemma approx_K_approx: approx = K.approx.
  Proof.
    extensionality n p.
    apply pred_ext'; intros w.
    unfold approx, compose; simpl.
    rewrite K.approx_spec.
    unfold rmap_level, unsquash; simpl;
    repeat rewrite K.knot_level;
    repeat rewrite setset, setget;     intuition.
  Qed.

  Lemma unsquash_squash : forall n rm, (unsquash (squash (n,rm))) = (n,rmap_fmap (approx n) (approx n) rm).
  Proof.
    intros.
    unfold unsquash, squash.
    rewrite K.unsquash_squash. unfold K.KI.F, f_pre_rmap.
    match goal with [|- (_,?X) = (_,?Y) ] =>
      replace Y with X; auto
    end.
    match goal with [|- pre_rmap2rmap' ?X = _ ] =>
      replace X with
        (fmap f_pre_rmap (K.approx n) (K.approx n) (rmap'2pre_rmap rm))
    end.
    2: repeat rewrite <- fmap_comp.
    2: unfold compose; auto.
    destruct rm; simpl.
    apply exist_ext.
    destruct x; simpl; f_equal.
    extensionality l.
    unfold compose.
    destruct (r l); simpl; auto.
    (* YES *)
    destruct p; simpl.
    rewrite approx_K_approx; auto.
    (* PURE *)
    destruct p; simpl.
    rewrite approx_K_approx; auto.
    (* ghost *)
    destruct g; simpl.
    apply ghost_ext; auto.
    extensionality i m.
    destruct (pds i m) as [[]|]; auto; simpl.
    rewrite approx_K_approx; auto.
  Qed.

  Instance Join_nat_rmap': Join (nat * rmap') := Join_prod _ (Join_equiv nat) _ _.
(*
Lemma fmap_p2p'_inj:
  forall p q,
        fmap SM.preds K.predicate K.predicate (@pred rmap ag_rmap) p =
        fmap SM.preds K.predicate K.predicate (@pred rmap ag_rmap) q ->
        p=q.
Proof.
  intros.
  destruct p as [p Vp]. destruct q as [q Vq].
  unfold fmap in *. unfold f_preds in *. simpl in *.
  inv H.
  f_equal.
  apply inj_pair2 in H2. unfold ffun_fmap, f_identity in *.
  unfold fmap, compose in H2.
  extensionality w.
 apply equal_f with w in H2. unfold fidentity_fmap in *.
  unfold p2p' in *. inv H2.
  unfold K.predicate in *.
  apply pred_ext'. intros [k o]. destruct o.
  apply equal_f with k in H0. rewrite H0; intuition.
Qed.
*)
  Lemma join_unsquash : forall phi1 phi2 phi3,
    join phi1 phi2 phi3 <->
    join (unsquash phi1) (unsquash phi2) (unsquash phi3).
  Proof.
    intros.
    unfold unsquash.
    rewrite KSa.join_unsquash.
    destruct (K.unsquash phi1) as [n f].
    destruct (K.unsquash phi2) as [n0 f0].
    destruct (K.unsquash phi3) as [n1 f1].
    simpl; intuition.
    destruct H; simpl in *; split; simpl; auto.
    inversion H0.
    constructor.
    intro l; spec H1 l.
    destruct f as [f ?].
    destruct f0 as [f0 ?].
    destruct f1 as [f1 ?].
    simpl in *.
    unfold compose.
    destruct f, f0, f1; simpl in *.
    inv H1; simpl.
    constructor; auto.
    destruct p. simpl in *. constructor; auto. destruct p. simpl in *. constructor; auto.
    destruct p; simpl in *.
    constructor; auto.
    destruct p; simpl in *.
    constructor; auto.

    destruct f, f0, f1; simpl in *.
    destruct x, x0, x1; simpl in *; inv H2; simpl.
    constructor; auto.
    intros i m; specialize (H4 i m); inv H4; constructor.
    inv H7; auto.

    destruct H; simpl in *; split; simpl; auto.
    destruct f as [f ?].
    destruct f0 as [f0 ?].
    destruct f1 as [f1 ?].
    inversion H0.
    hnf in H1. simpl proj1_sig in H1.
    constructor; auto.
    intro l; spec H1 l.
    simpl proj1_sig.
    clear - H1.
    destruct f, f0, f1; simpl in *.
    forget (r l) as a; forget (r0 l) as b; forget (r1 l) as c.
    clear - H1.
    unfold res2resource in *. unfold res_fmap in *.
    destruct a as [ra | ra sha ka pa| ka pa]; try destruct pa as [? ?p];
    destruct b as [rb | rb shb kb pb|kb pb]; try destruct pb as [? ?p];
    destruct c as [rc | rc shc kc pc|kc pc]; try destruct pc as [? ?p];
    inv H1.
    + constructor; auto.
    + apply inj_pair2 in H8. subst p0. constructor; auto.
    + apply inj_pair2 in H8. subst p0. constructor; auto.
    + subst. apply inj_pair2 in H11. subst p1. apply inj_pair2 in H7; subst p0.
      constructor; auto.
    + subst ; apply inj_pair2 in H8. subst p1. apply inj_pair2 in H5. subst p0.
      constructor; auto.
    + simpl in *.
      destruct f, f0, f1; simpl in *.
      destruct g, g0, g1; simpl in *.
      inv H2.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
        subst); constructor; auto.
      intros i m; specialize (H16 i m); inv H16; destruct (pds i m), (pds0 i m), (pds1 i m);
        try discriminate; try constructor.
      * destruct s, s0; inv H6; constructor.
      * destruct s, s0; inv H6; constructor.
      * inv H2; inv H3; inv H4.
        destruct s, s0, s1; inv H6.
        inv H3; inv H2; auto.
  Qed.

  Lemma ghost_of_core : forall phi, ghost_of (core phi) = core (ghost_of phi).
  Proof.
    intro; rewrite KSa.core_unsquash.
    unfold ghost_of, KSa.K.unsquash, KSa.K.squash, unsquash, squash.
    destruct (K.unsquash phi); simpl.
    rewrite K.unsquash_squash.
    destruct (pre_rmap_core _ _f).
    setoid_rewrite H; simpl.
    destruct _f as [[]]; simpl.
    destruct _f0; simpl.
    apply ghost_ext; auto.
  Qed.

  Definition rmap_age1 (k:rmap) : option rmap :=
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Definition rmap_unage (k:rmap) : rmap :=
    match unsquash k with
    | (n,x) => squash (S n, x)
    end.

  Lemma rmap_age1_knot_age1 :
    rmap_age1 = @age1 _ K.ageable_knot.
  Proof.
    extensionality x.
    unfold rmap_age1.
    rewrite  K.knot_age1.
    unfold unsquash, squash.
    case (K.unsquash x); simpl; intros.
    destruct n; auto.
    rewrite rmap'2pre_rmap2rmap'.
    f_equal.
  Qed.

  Lemma rmap_age1_eq: @age1 _ ag_rmap = rmap_age1.
  Proof.
   unfold age1. unfold ag_rmap; simpl; auto.
   rewrite rmap_age1_knot_age1; reflexivity.
  Qed.

  Lemma rmap_level_eq: @level rmap ag_rmap = fun x => fst (unsquash x).
  Proof.
    intros.
   extensionality x.  unfold level.  unfold ag_rmap.
   unfold KSa.K.ageable_knot. unfold unsquash.
   rewrite K.knot_level. destruct (K.unsquash x); simpl. auto.
  Qed.

(*  Lemma unevolve_identity_rmap :
   (* REMARK:  This may not be needed for anything, so for now it's removed
     from the Module Type *)
    forall w w':rmap, necR w w' -> identity w' -> identity w.
  Proof.
    intros.
    induction H; eauto.
    rewrite identity_unit_equiv in H0.
    rewrite identity_unit_equiv.
    red in H0. red.
    rewrite join_unsquash in H0.
    rewrite join_unsquash.
    hnf in H. unfold rmap, ag_rmap in H. rewrite <- rmap_age1_knot_age1 in H.
    unfold rmap_age1 in H.
   destruct (unsquash x).
   destruct n. inv H.
    assert (y = squash (n,r)).
    inv H; auto.
    subst y.
    rewrite unsquash_squash in H0.
    destruct H0.
    destruct H1.
    split; auto.
    split.
    intro l; spec H1 l.
    destruct r.
    simpl in *.
    unfold compose in *.
    destruct (fst x0 l); simpl in *.
    constructor; auto.
    inv H1; auto.
    inv H1. constructor; auto.
    constructor.
    simpl in *.
  Qed.*)

End Rmaps.
Local Close Scope nat_scope.

