Require Import msl.msl_standard.
Require Import msl.Coqlib2.
Import MixVariantFunctor.
Import MixVariantFunctorLemmas.
Import MixVariantFunctorGenerator.

Module Type ADR_VAL.
Parameter address : Type.
Parameter some_address:address.

(* Validity of traces.  The "valid" predicate ensures that related addresses don't get
    split apart from each other.  *)
Parameter kind: Type.
Parameter valid : (address -> option (pshare * kind)) -> Prop.
Parameter valid_empty: valid (fun _ => None).
Parameter valid_join: forall f g h : address -> option (pshare * kind),
   @join _ (Join_fun address (option (pshare * kind))
                   (Join_lower (Join_prod pshare Join_pshare kind (Join_equiv kind))))
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
  Definition valid (_: address -> option (pshare * kind)) := True.
  Lemma valid_empty: valid (fun _ => None).
  Proof. unfold valid; auto. Qed.
  Lemma valid_join: forall f g h : address -> option (pshare * kind),
   @join _ (Join_fun address (option (pshare * kind))
                   (Join_lower (Join_prod pshare Join_pshare kind (Join_equiv kind))))
      f g h  ->
    valid f -> valid g -> valid h.
  Proof.  intros; unfold valid; auto. Qed.
End SimpleAdrVal.

Fixpoint listprod (ts: list Type) : Type :=
 match ts with
  | nil => unit
  | t :: ts' => prod t (listprod ts')
 end.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
  Import AV.

  Definition preds: functor := fsig (fun A: list Type =>
    ffunc (fconst (listprod A)) fidentity).

  (*
  Goal forall PRED, preds PRED = { A: list Type & (listprod A -> PRED) }.
    intros. reflexivity. Qed.
  *)

  Inductive res (PRED : Type) : Type :=
    | NO':  Share.t -> res PRED
    | YES': Share.t -> pshare -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh => NO' B rsh
      | YES' rsh sh k pds => YES' B rsh sh k (fmap preds f g pds)
      | PURE' k pds => PURE' B k (fmap preds f g pds)
    end.
  Axiom ff_res : functorFacts res res_fmap.
  Definition f_res : functor := Functor ff_res.
  
  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall rsh1 rsh2 rsh3,
                               join rsh1 rsh2 rsh3 ->
                               res_join PRED (NO' PRED rsh1) (NO' PRED rsh2) (NO' PRED rsh3)
    | res_join_NO2 : forall rsh1 rsh2 rsh3 sh k p, 
                               join rsh1 rsh2 rsh3 ->
                               res_join PRED (NO' PRED rsh1) (YES' PRED rsh2 sh k p) (YES' PRED rsh3 sh k p)
    | res_join_NO3 : forall rsh1 rsh2 rsh3 sh k p, 
                               join rsh1 rsh2 rsh3 ->
                               res_join PRED (YES' PRED rsh1 sh k p) (NO' PRED rsh2 ) (YES' PRED rsh3 sh k p)
    | res_join_YES : forall (rsh1 rsh2 rsh3: Share.t) (sh1 sh2 sh3:pshare) k p,
                               join rsh1 rsh2 rsh3 ->
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED rsh1 sh1 k p) (YES' PRED rsh2 sh2 k p) (YES' PRED rsh3 sh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).
  Axiom pa_rj : forall PRED, @Perm_alg _ (res_join PRED).
  Axiom sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
  Axiom ca_rj : forall PRED, @Canc_alg _ (res_join PRED).
  Axiom da_rj : forall PRED, @Disj_alg _ (res_join PRED).
  Axiom paf_res : @pafunctor f_res res_join.
  
  Definition res_option (PRED : Type) (r: res PRED) :=
    match r with
      | NO' _ => None
      | YES' _ sh k _ => Some (sh,k)
      | PURE' _ _ => None (* PUREs cannot be split in any interesting way, which is what valid is about. *)
    end.
  
  Definition valid' A (w: address -> res A) : Prop :=
    AV.valid (fun l => res_option A (w l)).

  Axiom valid'_res_map : forall A B f g m,
    valid' A m -> valid' B (fmap f_res f g oo m).

  (* Definition pre_rmap (A:Type) := { m:address -> res A | valid' A m }. *)
  Definition f_pre_rmap : functor :=
    fsubset (ffunc (fconst address) f_res) _ valid'_res_map.

  (* TODO: this one not used? *)
  Axiom valid'_res_map2 : forall A B f g m, valid' B (res_fmap A B f g oo m) -> valid' A m.

  Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A) :=
            Join_prop _ (Join_fun address (res A) (res_join A)) (valid' A).

  Parameter Perm_pre_rmap: forall (A: Type), Perm_alg (f_pre_rmap A).
  Parameter Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter Canc_pre_rmap: forall (A: Type), Canc_alg (f_pre_rmap A).
  Parameter Disj_pre_rmap: forall (A: Type), Disj_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.

  Definition preds: functor := fsig (fun A: list Type =>
    ffunc (fconst (listprod A)) fidentity).

  Inductive res (PRED : Type) : Type :=
    | NO':  Share.t -> res PRED
    | YES': Share.t -> pshare -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh => NO' B rsh
      | YES' rsh sh k pds => YES' B rsh sh k (fmap preds f g pds)
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
    | res_join_NO1 : forall rsh1 rsh2 rsh3,
                               join rsh1 rsh2 rsh3 ->
                               res_join PRED (NO' PRED rsh1) (NO' PRED rsh2) (NO' PRED rsh3)
    | res_join_NO2 : forall rsh1 rsh2 rsh3 sh k p, 
                               join rsh1 rsh2 rsh3 ->
                               res_join PRED (NO' PRED rsh1) (YES' PRED rsh2 sh k p) (YES' PRED rsh3 sh k p)
    | res_join_NO3 : forall rsh1 rsh2 rsh3 sh k p, 
                               join rsh1 rsh2 rsh3 ->
                               res_join PRED (YES' PRED rsh1 sh k p) (NO' PRED rsh2 ) (YES' PRED rsh3 sh k p)
    | res_join_YES : forall (rsh1 rsh2 rsh3: Share.t) (sh1 sh2 sh3:pshare) k p,
                               join rsh1 rsh2 rsh3 ->
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED rsh1 sh1 k p) (YES' PRED rsh2 sh2 k p) (YES' PRED rsh3 sh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).

  Instance Join_res (PRED: Type) : Join (res PRED) := res_join PRED.

  Instance pa_rj : forall PRED, @Perm_alg _ (res_join PRED).
  Proof. intros. constructor.

      (* saf_eq *)
      intros x y z z' H1 H2; inv H1; inv H2; repeat f_equal; eapply join_eq; eauto.
  
      (* saf_assoc *)
      intros a b c d e H1 H2.
      destruct d as [rd | rd sd kd pd | kd pd].
      destruct a as [ra | | ]; try solve [elimtype False; inv H1].
      destruct b as [rb| | ]; try solve [elimtype False; inv H1].
      assert (join ra rb rd) by (inv H1; auto).
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO' _ rf); split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf sc kc pc).
      inv H2. split; constructor; auto.
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      destruct b as [ | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf sd kd pd).  inv H1; inv H2; split; constructor; auto.
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO' _ rf).  inv H1; inv H2; split; constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf sb kb pb).  inv H1; inv H2; split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf sc kc pc).  inv H1; inv H2; split; constructor; auto.
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES' _ rf se kb pb).  inv H1; inv H2; split; try constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      assert (H5: join sa sb sd) by (inv H1; auto).
      assert (H6: join sd sc se) by (inv H2; auto).
      destruct (join_assoc H5 H6) as [sf [? ?]].
      exists (YES' _ rf sf kb pb).  inv H1; inv H2; split; try constructor; auto.
      exists (PURE' _ kd pd). inv H1; inv H2; split; constructor.

      (* saf_com *)
      intros a b c H; inv H; econstructor;  apply join_comm; auto.

     (* saf_positivity *)
     intros; inv H; inv H0; auto; f_equal; eapply join_positivity; eauto.
 Qed.

  Instance sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
  Proof. intros.
            apply mkSep with (fun x => match x with NO' _ => NO' _ Share.bot | YES' _ _ _ _ => NO' _ Share.bot| PURE' k pds => PURE' _ k pds end).
            intro. destruct t; constructor; try apply join_unit1; auto.
            intros. inversion H; auto.
  Defined.

  Instance ca_rj : forall PRED, @Canc_alg _ (res_join PRED).
  Proof. repeat intro. inv H; inv H0; auto.
    f_equal. eapply join_canc; eauto.
    f_equal. eapply join_canc; eauto.
    apply no_units in H9; contradiction.
    f_equal. eapply join_canc; eauto.
    apply no_units in H2; contradiction.
    f_equal; eapply join_canc; eauto.
  Qed.

  Instance da_rj : forall PRED, @Disj_alg _ (res_join PRED).
  Proof.  repeat intro.
    inv H; f_equal; auto; apply join_self; auto.
  Qed.

  Definition paf_res : @pafunctor f_res res_join.
  Proof. constructor; repeat intro.
  (* This is a little painful because of the way res_join is defined, but
      whatever... *)
   inv H; simpl; constructor; trivial.
   destruct z as [ rz | rz sz kz pz | kz pz ].
   destruct x' as [ rx' | rx' sx' kx' px' | kx' px' ]; try solve [elimtype False; inv H].
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   exists (NO' _ rx'); exists (NO' _ ry); inv H; split; constructor; tauto.    
   destruct x' as [ rx' | rx' sx' kx' px' | kx' px' ]; try solve [elimtype False; inv H].
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
    exists (NO' _ rx'); exists (YES' _ ry sy kz pz); inv H; split; constructor; auto. simpl in *; f_equal; auto.
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   exists (YES' _ rx' sx' kx' pz); exists (NO' _ ry); inv H; split; constructor; auto.
   exists (YES' _ rx' sx' kx' pz); exists (YES' _ ry sy ky pz); inv H; split; constructor; auto; simpl; f_equal; auto.
   exists (PURE' _ kz pz); exists (PURE' _ kz pz); simpl in *; inv H; split; [constructor | tauto].

   destruct x as [ rx | rx sx kx px | kx px ]; try solve [elimtype False; inv H].
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (NO' _ ry); exists (NO' _ rz); inv H; split; constructor; auto.
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (YES' _ ry sy ky py); exists (YES' _ rz sy ky py); inv H; split; constructor; auto.
   destruct y as [ ry | ry sy ky py | ky py ]; try solve [elimtype False; inv H].
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (NO' _ ry); exists (YES' _ rz sx kx px); inv H; split; constructor; auto.
   destruct z' as [ rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
   exists (YES' _ ry sy kx px); exists (YES' _ rz sz kx px); inv H; split; constructor; auto. simpl; f_equal; auto.
   exists (PURE' _ kx px); exists (PURE' _ kx px); inv H; split; constructor; auto.
  Qed.
  
  Definition res_option (PRED : Type) (r: res PRED) :=
    match r with
      | NO' _ => None
      | YES' _ sh k _ => Some (sh,k)
      | PURE' _ _ => None (* PUREs cannot be split in any interesting way, which is what valid is about. *)
    end.
  
  Definition valid' A (w: address -> res A) : Prop :=
    AV.valid (fun l => res_option A (w l)).

  Lemma same_valid : forall f1 f2, (forall x, f1 x = f2 x) -> AV.valid f1 -> AV.valid f2.
  Proof.
    intros; replace f2 with f1; trivial.
    apply extensionality; auto.
  Qed.

  Lemma valid'_res_map : forall A B f g m,
    valid' A m -> valid' B (fmap f_res f g oo m).
  Proof.
    unfold valid'; intros A B f g m.
    apply same_valid; intro l.
    unfold compose.
    destruct (m l); simpl; auto.
  Qed.

  Lemma valid'_res_map2 : forall A B f g m,
    valid' B (fmap f_res f g oo m) -> valid' A m.
  Proof.
    unfold valid'; intros A B f g m.
    apply same_valid; intro l.
    unfold compose.
    destruct (m l); simpl; auto.
  Qed.

  Definition pre_rmap (A:Type) := { m:address -> res A | valid' A m }.
  Definition f_pre_rmap : functor :=
    fsubset (ffunc (fconst address) f_res) _ valid'_res_map.

  Instance Join_pre_rmap (A: Type) : Join (pre_rmap A) :=
            Join_prop _ (Join_fun address (res A) (res_join A)) (valid' A).

  Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap :=
    paf_subset (paf_fun address paf_res) valid' valid'_res_map valid'_res_map2.

  Lemma pre_rmap_sa_valid_core (A: Type):
        forall x : address -> res A,
       valid' A x ->
       valid' A  (@core (address -> res A) (Join_fun address (res A) (res_join A))
                     (Sep_fun address (res A) (res_join A) (sa_rj A)) x).
  Proof.
    intros. red. red.
    replace (fun l => res_option A (core x l)) with (fun l : address => @None (pshare * kind)).
    apply AV.valid_empty.
    extensionality a. simpl. icase (x a).
  Qed.


  Lemma pre_rmap_sa_valid_join : forall A (x y z : address -> res A),
    @join _ (Join_fun address (res A) (res_join A)) x y z ->
    valid' A x -> valid' A y -> valid' A z.
  Proof.
     intros.
     simpl in H.
     unfold valid' in *.
     apply AV.valid_join with (fun l => res_option A (x l)) (fun l => res_option A (y l)); auto.
     intro l. spec H l. inv H; try constructor. split; simpl; auto.
  Qed.

  Definition Perm_pre_rmap (A: Type): Perm_alg (pre_rmap A) :=
    Perm_prop _ _ (Perm_fun address _ _ _) _ (pre_rmap_sa_valid_join _).

  Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A) :=
    Sep_prop _ _ (Perm_fun address _ _ _) _ (pre_rmap_sa_valid_join _)  _ (pre_rmap_sa_valid_core _).

  Definition Canc_pre_rmap (A: Type): Canc_alg (pre_rmap A) :=
    @Canc_prop _ _ _ (Canc_fun address _ _ _).

  Definition Disj_pre_rmap (A: Type): Disj_alg (pre_rmap A) :=
    @Disj_prop _ _ _ (Disj_fun address _ _ _).

End StratModel.

Open Local Scope nat_scope.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.
  Import AV.

  Parameter rmap : Type.
  Axiom Join_rmap: Join rmap. Existing Instance Join_rmap.
  Axiom Perm_rmap: Perm_alg rmap. Existing Instance Perm_rmap.
  Axiom Sep_rmap: Sep_alg rmap. Existing Instance Sep_rmap.
  Axiom Canc_rmap: Canc_alg rmap.  Existing Instance Canc_rmap.
  Axiom Disj_rmap: Disj_alg rmap.  Existing Instance Disj_rmap.
  Axiom ag_rmap: ageable rmap.  Existing Instance ag_rmap.
  Axiom Age_rmap: Age_alg rmap.  Existing Instance Age_rmap.

  Inductive preds : Type :=
    SomeP : forall A : list Type, (listprod A -> pred rmap) -> preds.

  Definition NoneP := SomeP ((Void:Type)::nil) (fun _ => FF).

  Inductive resource : Type :=
    | NO: Share.t -> resource
    | YES: Share.t -> pshare -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.

  Definition res_option (r:resource) :=
    match r with
      | NO _ => None
      | YES _ sh k _ => Some (sh,k)
      | PURE k _ => None
    end.

  Inductive res_join : resource -> resource -> resource -> Prop :=
   | res_join_NO1 : forall rsh1 rsh2 rsh3
                               (RJ: join rsh1 rsh2 rsh3),
                               res_join (NO rsh1) (NO rsh2) (NO rsh3)
   | res_join_NO2 : forall rsh1 rsh2 rsh3 sh k p
                               (RJ: join rsh1 rsh2 rsh3), 
                               res_join (YES rsh1 sh k p) (NO rsh2) (YES rsh3 sh k p) 
   | res_join_NO3 : forall rsh1 rsh2 rsh3 sh k p
                               (RJ: join rsh1 rsh2 rsh3),
                               res_join (NO rsh1) (YES rsh2 sh k p) (YES rsh3 sh k p) 
   | res_join_YES : forall rsh1 rsh2 rsh3 (sh1 sh2 sh3:pshare) k p
                               (RJ: join rsh1 rsh2 rsh3),
                               join sh1 sh2 sh3 -> 
        res_join (YES rsh1 sh1 k p) (YES rsh2 sh2 k p) (YES rsh3 sh3 k p)
   | res_join_PURE : forall k p, res_join (PURE k p) (PURE k p) (PURE k p). 

  Instance Join_resource: Join resource := res_join.
  Axiom Perm_resource: Perm_alg resource. Existing Instance Perm_resource.
  Axiom Sep_resource: Sep_alg resource. Existing Instance Sep_resource.
  Axiom Canc_resource: Canc_alg resource. Existing Instance Canc_resource.
  Axiom Disj_resource: Disj_alg resource. Existing Instance Disj_resource.

  Definition preds_fmap (f g: pred rmap -> pred rmap) (x:preds) : preds :=
    match x with SomeP A Q => SomeP A (f oo Q)
    end.
  (* Check whether the following two can be erased. *)
  Axiom preds_fmap_id : preds_fmap (id _) (id _) = id preds.
  Axiom preds_fmap_comp : forall f1 f2 g1 g2,
    preds_fmap g1 g2 oo preds_fmap f1 f2 = preds_fmap (g1 oo f1) (f2 oo g2).

  Definition resource_fmap (f g:pred rmap -> pred rmap) (x:resource) : resource :=
    match x with
    | NO rsh => NO rsh
    | YES rsh sh k p => YES rsh sh k (preds_fmap f g p)
    | PURE k p => PURE k (preds_fmap f g p)
    end.
  Axiom resource_fmap_id : resource_fmap (id _) (id _) = id resource.
  Axiom resource_fmap_comp : forall f1 f2 g1 g2,
    resource_fmap g1 g2 oo resource_fmap f1 f2 = resource_fmap (g1 oo f1) (f2 oo g2).

  Definition valid (m: address -> resource) : Prop :=
    AV.valid  (res_option oo m).

  Axiom valid_res_map : forall f g m, valid m -> valid (resource_fmap f g oo m).
  Axiom rmapj_valid_join : forall (x y z : address -> resource),
    join x y z -> valid x -> valid y -> valid z.
  Axiom rmapj_valid_core: forall x: address -> resource, valid x -> valid (core x).

  Definition rmap' := sig valid. 

  Definition rmap_fmap (f g: pred rmap -> pred rmap) (x:rmap') : rmap' :=
    match x with exist m H => exist (fun m => valid m) (resource_fmap f g oo m) (valid_res_map f g m H) end.
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

  Definition resource_at (phi:rmap) : address -> resource := proj1_sig (snd (unsquash phi)).
  Infix "@" := resource_at (at level 50, no associativity).

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

End RMAPS.

Module Rmaps (AV':ADR_VAL) : RMAPS with Module AV:=AV'.
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
    Definition Canc_F := Canc_pre_rmap.
    Definition Disj_F := Disj_pre_rmap.
    Definition paf_F := paf_pre_rmap.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).
  Module KL := KnotLemmas_MixVariantHeredProp(K).
  Module KSa := KnotFullSa(TyFSA)(K)(KL).

  Definition rmap := K.knot.
  Instance Join_rmap: Join rmap := KSa.Join_knot.
  Instance Perm_rmap : Perm_alg rmap:= KSa.Perm_knot.
  Instance Sep_rmap : Sep_alg rmap:= KSa.Sep_knot. 
  Instance Canc_rmap : Canc_alg rmap:= KSa.Canc_knot.
  Instance Disj_rmap : Disj_alg rmap:= KSa.Disj_knot.
  Instance ag_rmap : ageable rmap := K.ageable_knot.
  Instance Age_rmap: Age_alg rmap := KSa.asa_knot.

  Inductive preds : Type :=
    SomeP : forall A : list Type, (listprod A -> pred rmap) -> preds.

  Definition NoneP := SomeP ((Void:Type)::nil) (fun _ => FF).

  Inductive resource : Type :=
    | NO: Share.t -> resource
    | YES: Share.t -> pshare -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.

  Definition resource2res (r: resource): res (pred rmap) :=
    match r with
      | NO rsh => NO' (pred rmap) rsh
      | YES rsh p k (SomeP A l) => YES' (pred rmap) rsh p k (existT _ A l)
      | PURE k (SomeP A l) => PURE' (pred rmap) k (existT _ A l)
    end.

  Definition res2resource (r: res (pred rmap)) : resource :=
    match r with
      | NO' rsh => NO rsh
      | YES' rsh p k (existT A l) => YES rsh p k (SomeP A l)
      | PURE' k (existT A l) => PURE k (SomeP A l)
    end.

  Lemma res2resource2res: forall x, resource2res (res2resource x) = x.
  Proof. unfold resource2res, res2resource; destruct x as [? | ? ? ? [? ?] | ? [? ?]]; auto. Qed.

  Lemma resource2res2resource: forall x, res2resource (resource2res x) = x.
  Proof. unfold resource2res, res2resource; destruct x; try destruct p0; try destruct p; auto. Qed.

  Definition res_option (r:resource) :=
    match r with
      | NO _ => None
      | YES _ sh k _ => Some (sh,k)
      | PURE _ _ => None
    end.

  Lemma res_option_rewrite: res_option = SM.res_option (pred rmap) oo resource2res.
  Proof. extensionality r; destruct r; auto. destruct p0; auto. destruct p; auto. Qed.

  Definition valid (m: address -> resource) : Prop :=
    AV.valid (res_option oo m).
  Inductive res_join : resource -> resource -> resource -> Prop :=
   | res_join_NO1 : forall rsh1 rsh2 rsh3
                               (RJ: join rsh1 rsh2 rsh3),
                               res_join (NO rsh1) (NO rsh2) (NO rsh3)
   | res_join_NO2 : forall rsh1 rsh2 rsh3 sh k p
                               (RJ: join rsh1 rsh2 rsh3), 
                               res_join (YES rsh1 sh k p) (NO rsh2) (YES rsh3 sh k p) 
   | res_join_NO3 : forall rsh1 rsh2 rsh3 sh k p
                               (RJ: join rsh1 rsh2 rsh3),
                               res_join (NO rsh1) (YES rsh2 sh k p) (YES rsh3 sh k p) 
   | res_join_YES : forall rsh1 rsh2 rsh3 (sh1 sh2 sh3:pshare) k p
                               (RJ: join rsh1 rsh2 rsh3),
                               join sh1 sh2 sh3 -> 
        res_join (YES rsh1 sh1 k p) (YES rsh2 sh2 k p) (YES rsh3 sh3 k p)
   | res_join_PURE : forall k p, res_join (PURE k p) (PURE k p) (PURE k p). 

  Instance Join_resource: Join resource := res_join.
  Instance Perm_resource: Perm_alg resource.
  Proof. constructor.

      (* saf_eq *)
      intros x y z z' H1 H2; inv H1; inv H2; repeat f_equal; eapply join_eq; eauto.
  
      (* saf_assoc *)
      intros a b c d e H1 H2.
      destruct d as [rd | rd sd kd pd | kd pd].
      destruct a as [ra | | ]; try solve [elimtype False; inv H1].
      destruct b as [rb| | ]; try solve [elimtype False; inv H1].
      assert (join ra rb rd) by (inv H1; auto).
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO rf); split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (join rd rc re) by (inv H2; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf sc kc pc).
      inv H2. split; constructor; auto.
      destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H2].
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      destruct b as [ | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf sd kd pd).  inv H1; inv H2; split; constructor; auto.
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (NO rf).  inv H1; inv H2; split; constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf sb kb pb).  inv H1; inv H2; split; constructor; auto.
      destruct e as [re | re se ke pe | ke pe]; try solve [elimtype False; inv H2].
      assert (H0: join rd rc re) by (inv H2; auto).
      destruct b as [ rb | rb sb kb pb | ]; try solve [elimtype False; inv H1].
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf sc kc pc).  inv H1; inv H2; split; constructor; auto.
      destruct a as [ra | ra sa ka pa | ka pa ]; try solve [elimtype False; inv H1].
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      exists (YES rf se kb pb).  inv H1; inv H2; split; try constructor; auto.
      assert (H: join ra rb rd) by (inv H1; auto).
      destruct (join_assoc H H0) as [rf [? ?]].
      assert (H5: join sa sb sd) by (inv H1; auto).
      assert (H6: join sd sc se) by (inv H2; auto).
      destruct (join_assoc H5 H6) as [sf [? ?]].
      exists (YES rf sf kb pb).  inv H1; inv H2; split; try constructor; auto.
      exists (PURE kd pd). inv H1; inv H2; split; constructor.

      (* saf_com *)
      intros a b c H; inv H; econstructor;  apply join_comm; auto.

     (* saf_positivity *)
     intros; inv H; inv H0; auto; f_equal; eapply join_positivity; eauto.
 Qed.

  Instance Sep_resource: Sep_alg resource.
  Proof.
    apply mkSep with (fun x => match x with NO _ => NO Share.bot | YES _ _ _ _ => NO Share.bot | PURE k pds => PURE k pds end).
    intros; destruct t; constructor; try apply join_unit1; auto.
    intros; inv H; auto.
  Defined.

  Instance Canc_resource: Canc_alg resource.
  Proof. repeat intro.
    inv H; inv H0; f_equal;
   try solve [   elimtype False; eapply no_units; eassumption];
   eapply join_canc; eassumption.
  Qed.

  Instance Disj_resource: Disj_alg resource.
  Proof.
    repeat intro. inv H; auto; f_equal; apply join_self; auto.
  Qed.

  Lemma same_valid : forall f1 f2, (forall x, f1 x = f2 x) -> AV.valid f1 -> AV.valid f2.
  Proof.
    intros; replace f2 with f1; trivial.
    apply extensionality; auto.
  Qed.

  Lemma rmapj_valid_core: forall x : address -> resource, valid x -> valid (core x).
  Proof.
     unfold valid, compose; intros. red. red. 
     replace (fun x0 => res_option (core x x0)) with (fun _ : address => @None (pshare * kind)).
     apply AV.valid_empty.
     extensionality a. simpl. icase (x a).
  Qed. 

  Lemma rmapj_valid_join : forall (x y z : address -> resource),
    join x y z ->
    valid x -> valid y -> valid z.
  Proof.
     intros.
     simpl in H.
     unfold valid, compose in *.
     apply AV.valid_join with (fun l => res_option (x l)) (fun l => res_option (y l)); auto.
     intro l. specialize (H l). inv  H; eauto. constructor. constructor. constructor.
     constructor. constructor. eauto. eauto.
     constructor.
  Qed.

  Definition rmap' := sig valid.
  Definition preds_fmap (f g:(pred rmap)->(pred rmap)) (x:preds) : preds :=
    match x with SomeP A ls => SomeP A (f oo ls) end.

  Lemma preds_fmap_id : preds_fmap (id (pred rmap)) (id (pred rmap)) = id preds.
  Proof.
    intros; apply extensionality; intro x; destruct x; simpl; auto;
    replace (id (pred rmap) oo p) with p; auto;
    rewrite id_unit2; auto.
  Qed.

  Lemma preds_fmap_comp : forall f1 f2 g1 g2,
    preds_fmap g1 g2 oo preds_fmap f1 f2 = preds_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros; apply extensionality; intro x; destruct x; simpl; auto.
  Qed.

  Definition resource_fmap (f g:pred rmap -> pred rmap) (x:resource) : resource :=
    match x with
    | NO rsh => NO rsh
    | YES rsh sh k p => YES rsh sh k (preds_fmap f g p)
    | PURE k p => PURE k (preds_fmap f g p)
    end.

  Lemma valid_res_map : forall f g m, valid m -> valid (resource_fmap f g oo m).
  Proof.
    unfold valid, compose; intros.
    replace (fun l : address => res_option (resource_fmap f g (m l)))
       with (fun l : address => res_option (m l)); auto.
    extensionality l.
    unfold res_option, resource_fmap.
    case (m l); auto.
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

  Lemma resource_fmap_comp : forall f1 f2 g1 g2,
    resource_fmap g1 g2 oo resource_fmap f1 f2 = resource_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros f1 f2 g1 g2.
    apply extensionality; intro x; destruct x; simpl; auto.
    unfold compose at 1; simpl.
    rewrite <- preds_fmap_comp; auto.
    rewrite <- preds_fmap_comp; auto.
  Qed.

  Definition rmap_fmap (f g:(pred rmap)->(pred rmap)) (x:rmap') : rmap' :=
    match x with exist m H => exist (fun m => valid m) (resource_fmap f g oo m) (valid_res_map f g m H) end.

  Lemma rmap_fmap_id : rmap_fmap (id (pred rmap)) (id (pred rmap)) = id rmap'.
  Proof.
    intros; apply extensionality; intro x.
    unfold rmap_fmap; destruct x.
    unfold id at 5.
    generalize (valid_res_map (id _) (id _) x v).
    rewrite (resource_fmap_id).
    simpl.
    rewrite (id_unit2 _ (resource) x).
    intro v0. f_equal; auto. apply proof_irr.
  Qed.

  Lemma rmap_fmap_comp : forall f1 f2 g1 g2,
    rmap_fmap g1 g2 oo rmap_fmap f1 f2 = rmap_fmap (g1 oo f1) (f2 oo g2).
  Proof.
    intros f1 f2 g1 g2.
    unfold rmap_fmap.
    apply extensionality; intro x.
    unfold compose at 1.
    destruct x.
    generalize (valid_res_map g1 g2 (resource_fmap f1 f2 oo x) (valid_res_map f1 f2 x v)).
    generalize (valid_res_map (g1 oo f1) (f2 oo g2) x v).
    clear.
    assert (resource_fmap g1 g2 oo resource_fmap f1 f2 oo x = resource_fmap (g1 oo f1) (f2 oo g2) oo x).
    rewrite <- compose_assoc.
    rewrite resource_fmap_comp; auto.
    rewrite H.
    intros.
    intros; f_equal; proof_irr; auto.
  Qed.

  Definition rmap'2pre_rmap (r: rmap') : f_pre_rmap (pred rmap).
    destruct r as [f ?].
    unfold f_pre_rmap.
    assert (valid' _ (fun x: address => resource2res (f x))).
    unfold valid'. unfold valid, compose in v.
    eapply same_valid; try apply v.
    intros. simpl.
    destruct (f x); simpl; auto. destruct p0; simpl; auto. destruct p; simpl; auto.
    eexists. exact H.
  Defined.

  Definition pre_rmap2rmap' (r: f_pre_rmap (pred rmap)) : rmap'.
    destruct r as [f ?].
    unfold rmap', valid' in *.
    assert (valid (fun l: address => res2resource (f l))).
    unfold valid, compose.
    replace (fun l : address => res_option (res2resource (f l))) with (fun l : address => SM.res_option (pred rmap) (f l)); auto.
    extensionality l. rewrite res_option_rewrite.
    unfold compose; simpl. rewrite res2resource2res. auto.
    eauto.
  Defined.

  Lemma rmap'2pre_rmap2rmap' :
    forall x, rmap'2pre_rmap (pre_rmap2rmap' x) = x.
  Proof.
    intro. destruct x as [f V]. unfold rmap'2pre_rmap, pre_rmap2rmap'. simpl.
    match goal with |- exist _ _ ?p = _ => generalize p; intro p1 end.
    apply exist_ext.
    extensionality x; rewrite res2resource2res; auto.
  Qed.

  Lemma pre_rmap2rmap'2pre_rmap :
    forall x,  pre_rmap2rmap' (rmap'2pre_rmap x) = x.
  Proof.
    intro.
    destruct x as [f V].
    unfold rmap'2pre_rmap, pre_rmap2rmap'. simpl.
    match goal with |- exist _ _ ?p = _ => generalize p; intro p1 end.
    apply exist_ext.
    extensionality x; rewrite resource2res2resource; auto.
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
  Definition resource_at (phi:rmap) : address -> resource := proj1_sig (snd (unsquash phi)).
  Infix "@" := resource_at (at level 50, no associativity).

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
    extensionality l.
    unfold compose.
    destruct (x l); simpl; auto.
    (* YES *)
    destruct p0; simpl.
    f_equal. f_equal.
    extensionality a. 
    apply pred_ext'; intro w.
    unfold approx, compose; simpl.
    rewrite K.approx_spec.
    unfold fidentity_fmap;
    unfold rmap_level, unsquash; simpl;
    repeat rewrite K.knot_level;
    repeat rewrite setset, setget;     intuition.
    (* PURE *)
    destruct p; simpl.
    f_equal. f_equal.
    extensionality a. 
    apply pred_ext'; intro w.
    unfold approx, compose; simpl.
    rewrite K.approx_spec.
    unfold fidentity_fmap;
    unfold rmap_level, unsquash; simpl;
    repeat rewrite K.knot_level;
    repeat rewrite setset, setget;     intuition.
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
    intro l; spec H0 l.
    destruct f as [f ?].
    destruct f0 as [f0 ?].
    destruct f1 as [f1 ?].
    simpl in *.
    unfold compose.
    inv H0; simpl.
    constructor; auto.
    destruct p. simpl in *. constructor; auto. destruct p. simpl in *. constructor; auto.
    destruct p; simpl in *.
    constructor; auto.
    destruct p; simpl in *.
    constructor; auto.

    destruct H; simpl in *; split; simpl; auto.
    destruct f as [f ?].
    destruct f0 as [f0 ?].
    destruct f1 as [f1 ?].
    hnf in H0. simpl proj1_sig in H0.
    intro l; spec H0 l.
    simpl proj1_sig.
    clear - H0.
    forget (f l) as a; forget (f0 l) as b; forget (f1 l) as c.
    clear - H0.
    unfold res2resource in *. unfold res_fmap in *.
    destruct a as [ra | ra sha ka pa| ka pa]; try destruct pa as [? ?p];
    destruct b as [rb | rb shb kb pb|kb pb]; try destruct pb as [? ?p];
    destruct c as [rc | rc shc kc pc|kc pc]; try destruct pc as [? ?p];
    inv H0.
    + constructor; auto.
    + apply inj_pair2 in H10. subst p0. constructor; auto.
    + apply inj_pair2 in H10. subst p0. constructor; auto.
    + subst x1. apply inj_pair2 in H14. subst p1. apply inj_pair2 in H9; subst p0.
      constructor; auto.
    + subst x1. apply inj_pair2 in H8. subst p1. apply inj_pair2 in H5. subst p0.
      constructor; auto.
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
 
  Lemma unevolve_identity_rmap :
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
    destruct H0; split;  simpl fst in *; simpl snd in *; try split; auto.
    intro l; spec H1 l.
    destruct r.
    simpl in *.
    unfold compose in *.
    destruct (x0 l); simpl in *.
    constructor; auto.
    inv H1; auto.
    inv H1. constructor; auto.
    constructor.
  Qed.

End Rmaps.
Local Close Scope nat_scope.

