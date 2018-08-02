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
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.

Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor :=
  fix dtfr (T: TypeTree): functor :=
  match T with
  | ConstType A => fconst A
  | Mpred => fidentity
  | DependentType n => fconst (nth n ts unit)
  | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
  | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
  | PiType _ f => fpi (fun i => dtfr (f i))
  | ListType T => flist (dtfr T)
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
  | ListType T => list (dtfr T)
  end.

Definition fpreds: functor :=
  fsig (fun T: TypeTree =>
    fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

Lemma realize_eq: forall {A} (a b: A) P, (exists H: a = b, P H) -> {H: a = b & P H}.
Proof.
  intros ???? []; subst; exists eq_refl; auto.
Qed.

Lemma lower_join_inv : forall {A} {J: Join A} a b c, lower_join J a b c <->
  match a, b, c with
  | Some a, Some b, Some c => join a b c
  | Some a, None, Some c | None, Some a, Some c => a = c
  | None, None, None => True
  | _, _, _ => False
  end.
Proof.
  split.
  - inversion 1; subst; auto; destruct c; auto.
  - destruct a, b, c; intros; subst; try contradiction; try constructor; auto.
Qed.

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

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
  Definition f_ghost : functor := Functor ff_ghost.

  Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join PRED : Join (ghost PRED) :=
  | ghost_join_nil_l m: ghost_join PRED nil m m
  | ghost_join_nil_r m: ghost_join PRED m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join PRED m1 m2 m3 ->
      ghost_join PRED (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Existing Instance ghost_join.

  Axiom pa_gj : forall PRED, @Perm_alg _ (ghost_join PRED).

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
  Proof.
    intros; exists (fun _ => nil); auto; constructor.
  Defined.
  Axiom paf_ghost : @pafunctor f_ghost ghost_join.

  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

  Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A) :=
            Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A).

  Declare Instance Perm_pre_rmap: forall (A: Type), Perm_alg (f_pre_rmap A).
  Declare Instance Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

  Existing Instance ghost_join.
  Instance Join_res A : Join (f_res A) := res_join A.

Axiom pre_rmap_core:
forall (A : Type) (m : f_pre_rmap A),
  @core (f_pre_rmap A) (Join_pre_rmap A) (Sep_pre_rmap A) m =
 (@core ((fpair (ffunc (fconst address) f_res) f_ghost) A)
           (Join_prod ((ffunc (fconst address) f_res) A)
              (Join_pi ((fconst address) A)
                 (fun _ : (fconst address) A => f_res A)
                 (fun _ : (fconst address) A => Join_res A))
              (f_ghost A) (ghost_join A))
           (@Sep_prod ((ffunc (fconst address) f_res) A)
              (Join_pi ((fconst address) A)
                 (fun _ : (fconst address) A => f_res A)
                 (fun _ : (fconst address) A => Join_res A))
              (f_ghost A) (ghost_join A)
              (Sep_pi ((fconst address) A)
                 (fun _ : (fconst address) A => f_res A)
                 (fun _ : (fconst address) A => Join_res A)
                 (fun _ : (fconst address) A => sa_rj A)) 
              (sa_gj A)) m).

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

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
  Proof.
    constructor; intros; extensionality x; unfold ghost_fmap.
    - rewrite fmap_id; auto.
    - rewrite <- fmap_comp; auto.
  Qed.

  Definition f_ghost : functor := Functor ff_ghost.

  Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join PRED : Join (ghost PRED) :=
  | ghost_join_nil_l m: ghost_join PRED nil m m
  | ghost_join_nil_r m: ghost_join PRED m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join PRED m1 m2 m3 ->
      ghost_join PRED (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Hint Constructors ghost_join.
  Existing Instance ghost_join.

  Lemma elem_join_inv: forall a1 a2 a3, ghost_elem_join a1 a2 a3 ->
  match a1, a2, a3 with
  | existT g1 (exist x1 _), existT g2 (exist x2 _), existT g3 (exist x3 _) =>
      exists H: g2 = g1, exists H': g3 = g1, join x1 (eq_rect _ _ x2 _ H) (eq_rect _ _ x3 _ H')
  end.
  Proof.
    inversion 1; subst.
    exists eq_refl, eq_refl; auto.
  Qed.

  Lemma ghost_join_inv: forall PRED m1 m2 m3, ghost_join PRED m1 m2 m3 ->
  match m1, m2 with
  | nil, _ => m3 = m2
  | _, nil => m3 = m1
  | a1 :: m1, a2 :: m2 => match m3 with nil => False
                          | a3 :: m3 => join a1 a2 a3 /\ ghost_join PRED m1 m2 m3 end
  end.
  Proof.
    induction 1; simpl; auto.
    destruct m; simpl; auto.
  Qed.

  Instance pa_gej : @Perm_alg _ ghost_elem_join.
  Proof.
    constructor.
    - inversion 1; inversion 1; subst.
      inv H.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst).
      f_equal; eapply exist_ext, join_eq; eauto.
    - intros ????? J1%elem_join_inv J2%elem_join_inv.
      destruct a as (ga & a & ?), b as (gb & b & ?), c as (gc & c & ?), d as (gd & d & ?),
        e as (ge & e & ?).
      repeat (apply realize_eq in J1; destruct J1 as [? J1]).
      repeat (apply realize_eq in J2; destruct J2 as [? J2]); subst.
      destruct (join_assoc J1 J2) as (f & ? & J).
      exists (existT _ ga (exist _ f (join_valid _ _ _ (join_comm J) v3))).
      split; constructor; auto.
    - inversion 1; constructor; auto.
    - inversion 1; subst; inversion 1; subst; auto.
      inv H.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst).
      f_equal; eapply exist_ext, join_positivity; eauto.
  Qed.

  Instance pa_gj : forall PRED, @Perm_alg _ (ghost_join PRED).
  Proof.
    constructor.
    - intros until 1; revert z'; induction H; inversion 1; subst; auto.
      f_equal; auto.
      eapply join_eq; eauto.
    - induction a; intros ???? J1 J2; apply ghost_join_inv in J1; subst.
      { exists e; split; auto; constructor. }
      destruct b; subst; [eexists; split; eauto; constructor|].
      destruct d; [contradiction|].
      destruct J1 as [Jc1 J1].
      apply ghost_join_inv in J2.
      destruct c; subst; [eexists; split; eauto; constructor; auto|].
      destruct e; [contradiction|].
      destruct J2 as [Jc2 J2].
      destruct (join_assoc Jc1 Jc2) as (f & ? & ?).
      destruct (IHa _ _ _ _ J1 J2) as (f' & ? & ?).
      exists (f :: f'); split; constructor; auto.
    - induction 1; constructor; auto.
    - intros until 1; revert b'; induction H; inversion 1; subst; auto.
      f_equal; eauto.
      eapply join_positivity; eauto.
  Qed.

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
  Proof.
    intros; exists (fun _ => nil); auto; constructor.
  Defined.

  Opaque fpreds.

  Definition paf_ghost : @pafunctor f_ghost ghost_join.
  Proof.
    constructor; repeat intro.
    - induction H; constructor; auto.
      inv H; constructor; auto.
      inv H1; constructor; auto.
      inv H2; constructor; auto; simpl; congruence.
    - revert dependent z; revert y; induction x'; intros; apply ghost_join_inv in H.
      { exists nil, z; split; auto; constructor. }
      destruct y; simpl in *.
      { exists z, nil; split; auto; constructor. }
      destruct z; [contradiction | simpl in *].
      destruct H as [J1 J2].
      destruct (IHx' _ _ J2) as (x & y' & ? & ? & ?); subst.
      apply lower_join_inv in J1.
      destruct a as [[[? []]]|].
      + destruct o as [[[? []]]|].
        * destruct o0 as [[[? []]]|]; [|contradiction].
          destruct J1 as [J1%elem_join_inv J1']; simpl in *.
          repeat (apply realize_eq in J1 as [? J1]); subst; simpl in *.
          exists (Some (existT _ x0 (exist _ _ v), _f1) :: x),
            (Some (existT _ x0 (exist _ _ v0), _f1) :: y').
          split; [repeat constructor; auto|].
          unfold ghost_fmap in *; simpl in *.
          inv J1'.
          rewrite <- H1, <- H2; auto.
        * destruct o0 as [[[? []]]|]; [|contradiction].
          inv J1.
          match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
            subst.
          exists (Some (existT _ x2 (exist _ _ v0), _f0) :: x), (None :: y').
          split; [repeat constructor; auto|].
          unfold ghost_fmap in *; simpl in *.
          rewrite <- H1; split; f_equal; f_equal; f_equal; f_equal.
          apply exist_ext; auto.
      + exists (None :: x), (o0 :: y').
        split; [repeat constructor; auto|].
        split; auto.
        unfold ghost_fmap in *; simpl in *.
        rewrite <- H1; f_equal.
        destruct o, o0; inv J1; auto.
    - revert dependent z'; revert y; induction x; intros; apply ghost_join_inv in H; simpl in H.
      { exists y, y; split; auto; constructor. }
      destruct y; simpl in *.
      { exists nil, (a :: x); split; auto; constructor. }
      destruct z'; [contradiction | simpl in *].
      destruct H as [J1 J2].
      destruct (IHx _ _ J2) as (y' & z & ? & ? & ?); subst.
      apply lower_join_inv in J1.
      destruct a as [[[? []]]|].
      + destruct o as [[[? []]]|].
        * destruct o0 as [[[? []]]|]; [|contradiction].
          destruct J1 as [J1%elem_join_inv J1']; simpl in *.
          repeat (apply realize_eq in J1 as [? J1]); subst; simpl in *.
          exists (Some (existT _ x0 (exist _ _ v0), _f) :: y'),
            (Some (existT _ x0 (exist _ _ v1), _f) :: z).
          split; [repeat constructor; auto|].
          unfold ghost_fmap in *; simpl in *.
          inv J1'.
          rewrite <- H0, <- H1; auto.
        * destruct o0 as [[[? []]]|]; [|contradiction].
          inv J1.
          match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
            subst.
          exists (None :: y'), (Some (existT _ x2 (exist _ _ v), _f) :: z).
          split; [repeat constructor; auto|].
          unfold ghost_fmap in *; simpl in *.
          rewrite <- H0; split; f_equal; f_equal; f_equal; f_equal.
          apply exist_ext; auto.
      + exists (o :: y'), (o :: z).
        split; [repeat constructor; auto|].
        unfold ghost_fmap in *; simpl in *; rewrite <- H0; split; f_equal.
        destruct o, o0; auto; contradiction.
  Qed.

  Definition pre_rmap (A:Type) := ((address -> res A) * ghost A)%type.
  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

  Notation Join_obj A := (Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A)).

  Instance Join_pre_rmap (A: Type) : Join (pre_rmap A) :=
    Join_obj A.

  Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap :=
    paf_pair (paf_fun address paf_res) paf_ghost.

  Definition Perm_pre_rmap (A: Type): Perm_alg (pre_rmap A) :=
    Perm_prod (Perm_fun address _ _ _) (pa_gj A).

  Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A) :=
    Sep_prod (Sep_fun address _ _ _) (sa_gj A).

Lemma pre_rmap_core:
forall (A : Type) (m : f_pre_rmap A),
  @core (f_pre_rmap A) (Join_pre_rmap A) (Sep_pre_rmap A) m =
 (@core ((fpair (ffunc (fconst address) f_res) f_ghost) A)
           (Join_prod ((ffunc (fconst address) f_res) A)
              (Join_pi ((fconst address) A)
                 (fun _ : (fconst address) A => f_res A)
                 (fun _ : (fconst address) A => Join_res A))
              (f_ghost A) (ghost_join A))
           (@Sep_prod ((ffunc (fconst address) f_res) A)
              (Join_pi ((fconst address) A)
                 (fun _ : (fconst address) A => f_res A)
                 (fun _ : (fconst address) A => Join_res A))
              (f_ghost A) (ghost_join A)
              (Sep_pi ((fconst address) A)
                 (fun _ : (fconst address) A => f_res A)
                 (fun _ : (fconst address) A => Join_res A)
                 (fun _ : (fconst address) A => sa_rj A)) 
              (sa_gj A)) m).
Proof.
intros. reflexivity.
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

  Definition resource_fmap (f g:pred rmap -> pred rmap) (x:resource) : resource :=
    match x with
    | NO sh nsh => NO sh nsh
    | YES sh rsh k p => YES sh rsh k (preds_fmap f g p)
    | PURE k p => PURE k (preds_fmap f g p)
    end.
  Axiom resource_fmap_id : resource_fmap (id _) (id _) = id resource.
  Axiom resource_fmap_comp : forall f1 f2 g1 g2,
    resource_fmap g1 g2 oo resource_fmap f1 f2 = resource_fmap (g1 oo f1) (f2 oo g2).

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Existing Instance ghost_join.

  Axiom Perm_ghost: Perm_alg ghost. Existing Instance Perm_ghost.
  Axiom Sep_ghost: Sep_alg ghost. Existing Instance Sep_ghost.
  Axiom ghost_core: forall (g: ghost), core g = nil.

  Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    map (option_map (fun '(a, b) => (a, preds_fmap f g b))) x.

  Axiom ghost_fmap_id : ghost_fmap (id _) (id _) = id ghost.
  Axiom ghost_fmap_comp : forall f1 f2 g1 g2,
    ghost_fmap g1 g2 oo ghost_fmap f1 f2 = ghost_fmap (g1 oo f1) (f2 oo g2).

  Definition rmap' := ((address -> resource) * ghost)%type.

  Definition rmap_fmap (f g: pred rmap -> pred rmap) (x:rmap') : rmap' :=
    (resource_fmap f g oo fst x, ghost_fmap f g (snd x)).

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

  Definition resource_at (phi:rmap) : address -> resource := fst (snd (unsquash phi)).
  Infix "@" := resource_at (at level 50, no associativity).
  Definition ghost_of (phi:rmap) : ghost := snd (snd (unsquash phi)).

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

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Definition pred2p (p: preds) : fpreds (pred rmap) :=
    match p with SomeP A P => existT _ A P end.

  Definition p2pred (p: fpreds (pred rmap)) : preds :=
    match p with existT A P => SomeP A P end.

  Definition ghost2g (r: ghost): SM.ghost (pred rmap) :=
    map (option_map (fun '(a, b) => (a, pred2p b))) r.

  Definition g2ghost (r: SM.ghost (pred rmap)) : ghost :=
    map (option_map (fun '(a, b) => (a, p2pred b))) r.

  Lemma g2ghost2g: forall x, ghost2g (g2ghost x) = x.
  Proof.
    induction x; auto; simpl.
    rewrite IHx; destruct a as [[]|]; auto; simpl.
    destruct _f; auto.
  Qed.

  Lemma ghost2g2ghost: forall x, g2ghost (ghost2g x) = x.
  Proof.
    induction x; auto; simpl.
    rewrite IHx; destruct a as [[]|]; auto; simpl.
    destruct p; auto.
  Qed.

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

  (* Will this give us the higher-order ghost state we want? *)
  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Existing Instance ghost_join.

  Lemma elem_join_inv: forall a1 a2 a3, ghost_elem_join a1 a2 a3 ->
  match a1, a2, a3 with
  | existT g1 (exist x1 _), existT g2 (exist x2 _), existT g3 (exist x3 _) =>
      exists H: g2 = g1, exists H': g3 = g1, join x1 (eq_rect _ _ x2 _ H) (eq_rect _ _ x3 _ H')
  end.
  Proof.
    inversion 1; subst.
    exists eq_refl, eq_refl; auto.
  Qed.

  Lemma ghost_join_inv: forall m1 m2 m3, ghost_join m1 m2 m3 ->
  match m1, m2 with
  | nil, _ => m3 = m2
  | _, nil => m3 = m1
  | a1 :: m1, a2 :: m2 => match m3 with nil => False
                          | a3 :: m3 => join a1 a2 a3 /\ ghost_join m1 m2 m3 end
  end.
  Proof.
    induction 1; simpl; auto.
    destruct m; simpl; auto.
  Qed.

  Instance pa_gej : @Perm_alg _ ghost_elem_join.
  Proof.
    constructor.
    - inversion 1; inversion 1; subst.
      inv H.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst).
      f_equal; eapply exist_ext, join_eq; eauto.
    - intros ????? J1%elem_join_inv J2%elem_join_inv.
      destruct a as (ga & a & ?), b as (gb & b & ?), c as (gc & c & ?), d as (gd & d & ?),
        e as (ge & e & ?).
      repeat (apply realize_eq in J1; destruct J1 as [? J1]).
      repeat (apply realize_eq in J2; destruct J2 as [? J2]); subst.
      destruct (join_assoc J1 J2) as (f & ? & J).
      exists (existT _ ga (exist _ f (join_valid _ _ _ (join_comm J) v3))).
      split; constructor; auto.
    - inversion 1; constructor; auto.
    - inversion 1; subst; inversion 1; subst; auto.
      inv H.
      repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
          subst).
      f_equal; eapply exist_ext, join_positivity; eauto.
  Qed.

  Instance Perm_ghost : Perm_alg ghost.
  Proof.
    constructor.
    - intros until 1; revert z'; induction H; inversion 1; subst; auto.
      f_equal; auto.
      eapply join_eq; eauto.
    - induction a; intros ???? J1 J2; apply ghost_join_inv in J1; subst.
      { exists e; split; auto; constructor. }
      destruct b; subst; [eexists; split; eauto; constructor|].
      destruct d; [contradiction|].
      destruct J1 as [Jc1 J1].
      apply ghost_join_inv in J2.
      destruct c; subst; [eexists; split; eauto; constructor; auto|].
      destruct e; [contradiction|].
      destruct J2 as [Jc2 J2].
      destruct (join_assoc Jc1 Jc2) as (f & ? & ?).
      destruct (IHa _ _ _ _ J1 J2) as (f' & ? & ?).
      exists (f :: f'); split; constructor; auto.
    - induction 1; constructor; auto.
    - intros until 1; revert b'; induction H; inversion 1; subst; auto.
      f_equal; eauto.
      eapply join_positivity; eauto.
  Qed.

  Instance Sep_ghost : Sep_alg ghost.
  Proof.
    intros; exists (fun _ => nil); auto; constructor.
  Defined.

  Lemma ghost_core : forall (g: ghost), core g = nil.
  Proof.
    auto.
  Qed.

  Definition rmap' := ((address->resource) * ghost)%type.
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

  Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    map (option_map (fun '(a, b) => (a, preds_fmap f g b))) x.

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
    extensionality x; induction x; auto; simpl.
    rewrite IHx; destruct a as [[]|]; auto; simpl.
    rewrite preds_fmap_id; auto.
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
    intros; extensionality x; induction x; auto; simpl.
    rewrite <- IHx; destruct a as [[]|]; auto; simpl.
    rewrite <- preds_fmap_comp; auto.
  Qed.

  Definition rmap_fmap (f g:(pred rmap)->(pred rmap)) (x:rmap') : rmap' :=
              (resource_fmap f g oo fst x, ghost_fmap f g (snd x)).

  Lemma rmap_fmap_id : rmap_fmap (id (pred rmap)) (id (pred rmap)) = id rmap'.
  Proof.
    intros; apply extensionality; intro x.
    unfold rmap_fmap; destruct x.
    simpl.
    rewrite resource_fmap_id, ghost_fmap_id.
    rewrite (id_unit2 _ (resource) r).
    f_equal; auto.
  Qed.

  Lemma rmap_fmap_comp : forall f1 f2 g1 g2,
    rmap_fmap g1 g2 oo rmap_fmap f1 f2 = rmap_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros f1 f2 g1 g2.
    unfold rmap_fmap.
    apply extensionality; intro x.
    unfold compose at 1.
    destruct x as (r,g). simpl.
    rewrite <- compose_assoc.
    rewrite resource_fmap_comp; auto.
    f_equal; auto.
    pose proof ghost_fmap_comp as HG.
    unfold compose in HG at 1; rewrite <- HG.
    intros.
    f_equal; proof_irr; auto.
  Qed.

  Definition rmap'2pre_rmap (f: rmap') : f_pre_rmap (pred rmap) :=
      (fun x : address => resource2res (fst f x), ghost2g (snd f)).

  Definition pre_rmap2rmap' (f: f_pre_rmap (pred rmap)) : rmap' :=
      (fun l : address => res2resource (fst f l), g2ghost (snd f)).

  Lemma rmap'2pre_rmap2rmap' :
    forall x, rmap'2pre_rmap (pre_rmap2rmap' x) = x.
  Proof.
    intro. unfold rmap'2pre_rmap, pre_rmap2rmap'. simpl.
    destruct x; simpl; f_equal.
    extensionality x; rewrite res2resource2res; auto.
    rewrite g2ghost2g; auto.
  Qed.

  Lemma pre_rmap2rmap'2pre_rmap :
    forall x,  pre_rmap2rmap' (rmap'2pre_rmap x) = x.
  Proof.
    intro.
    unfold rmap'2pre_rmap, pre_rmap2rmap'. simpl.
    destruct x; simpl; f_equal.
    extensionality x; rewrite resource2res2resource; auto.
    rewrite ghost2g2ghost; auto.
  Qed.

  Definition squash (n_rm:nat * rmap') : rmap :=
    match n_rm with (n,rm) => K.squash (n, rmap'2pre_rmap rm) end.

  Definition unsquash (phi:rmap) : (nat * rmap') :=
    match K.unsquash phi with (n,rm) => (n, pre_rmap2rmap' rm) end.

  Definition rmap_level (phi:rmap) : nat := fst (unsquash phi).
  Definition resource_at (phi:rmap) : address -> resource := fst (snd (unsquash phi)).
  Infix "@" := resource_at (at level 50, no associativity).
  Definition ghost_of (phi:rmap) : ghost := snd (snd (unsquash phi)).

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
    destruct rm; simpl. unfold pre_rmap2rmap', rmap_fmap. simpl; f_equal.
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
    induction g; auto; simpl.
    setoid_rewrite IHg; destruct a as [[]|]; auto; simpl.
    repeat f_equal.
    rewrite approx_K_approx; destruct p; auto.
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
  Lemma g2ghost_inv: forall g1 g2, g2ghost g1 = g2ghost g2 -> g1 = g2.
  Proof.
    induction g1; destruct g2; inversion 1; auto.
    f_equal; auto.
    destruct a as [[]|], o as [[]|]; inv H1; auto.
    destruct _f, _f0; inv H4; auto.
  Qed.

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
    intro l; specialize ( H1 l).
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
    clear - H2; induction H2; constructor; auto.
    inv H; constructor; auto.
    destruct a0, a4, a5; inv H0; simpl in *.
    inv H; inv H1; constructor; constructor; auto.

    destruct H; simpl in *; split; simpl; auto.
    inversion H0.
    hnf in H1. simpl proj1_sig in H1.
    constructor; auto.
    intro l; specialize ( H1 l).
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
      clear - H2.
      remember (g2ghost g) as a; remember (g2ghost g0) as b; remember (g2ghost g1) as c.
      revert dependent g1; revert dependent g0; revert dependent g; induction H2; intros; subst.
      * apply g2ghost_inv in Heqc; subst; destruct g; [constructor | discriminate].
      * apply g2ghost_inv in Heqc; subst; destruct g0; [constructor | discriminate].
      * destruct g, g0, g1; inv Heqa; inv Heqb; inv Heqc.
        constructor; [|apply IHghost_join; auto].
        destruct o as [[]|], o0 as [[]|], o1 as [[]|]; inv H; try constructor.
        -- destruct _f, _f0, _f1; inv H4; simpl in *.
           inv H; inv H0.
           inv H; inv H3.
           repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
             subst); constructor; constructor; auto.
        -- destruct _f, _f0; inv H4.
           repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
             subst); constructor; auto.
        -- destruct _f, _f0; inv H4.
           repeat (match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end;
             subst); constructor; auto.
  Qed.

  Lemma ghost_of_core : forall phi, ghost_of (core phi) = core (ghost_of phi).
  Proof.
    intro; rewrite KSa.core_unsquash.
    unfold ghost_of, KSa.K.unsquash, KSa.K.squash, unsquash, squash.
    destruct (K.unsquash phi); simpl.
    rewrite K.unsquash_squash; simpl.
    setoid_rewrite (pre_rmap_core _ _f). auto.
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
    intro l; specialize ( H1 l).
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

