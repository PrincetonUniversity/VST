From lithium Require Import simpl_classes.
From VST.typing Require Export base annotations.
Set Default Proof Using "Type".

Class typeG Σ := TypeG {
  type_heapG :: heapGS Σ;
}.

(*** type *)
(** There are different for how to model ownership in this type system
and there does not seem to be a perfect one. The options explored so
far are: (ty_own : own_state → loc → iProp Σ )

Owned and shared references:
Inductive own_state : Type := | Own | Shr.
ty_own Own l ={⊤\↑shrN}=∗ ty_own Shr l
Persistent (ty_own Shr l)

This is the simplest option but also the most restrictive:
Once a type is shared it is never possible to unshare it. This might
be enough for Hafnium though. But it seems hard to type e.g. RWLocks with this
model of types. This model is simple because there is no need for recombining
things which is a big source of problems in the other models.

guarded ty:
 Own: ▷ l ◁ₗ{Own} ty
 Shr: □ {|={⊤, ⊤\↑shrN}▷=> l ◁ₗ{Shr} ty
 This could work via the delayed sharing trick of Rustbelt
Lock ty:
 Own: l ↦ b ∗ (l +ₗ 1) ◁ₗ{Own} ty
 Shr: inv lockN (∃ b, l ↦ b ∗ if b then True else (l +ₗ 1) ◁ₗ{Own} ty)
LockGuard ty:
 Own: l ◁ₗ{Shr} Lock ty ∗ (l +ₗ 1) ◁ₗ{Own} ty
 Shr: False ???

Distinct owned and fractional references:
Inductive own_state : Type :=
| Own | Frac (q : Qp).
Definition own_state_to_frac (β : own_state) : Qp :=
  match β with
  | Own => 1%Qp
  | Frac q => q
  end.
Definition own_state_min (β1 β2 : own_state) : own_state :=
  match β1, β2 with
  | Own, Own => Own
  | Frac q, Own => Frac q
  | Own, Frac q => Frac q
  | Frac q, Frac q' => Frac (q * q')
  end.
ty_own Own l ={⊤}=∗ ty_own (Frac 1%Qp) l;
(* ={⊤,∅}▷=∗ would be too strong as we cannot prove it for structs *)
(* maybe you want ={⊤,⊤}▷=∗ here (to strip of the later when going from a frac lock to a owned lock) *
 I think that you actually want the later here since conceptually fractional is one later than the original one (see RustBelt)
 probably you don't want the viewshift after the later, only before it (see inheritance in RustBelt and cancellation of cancellable invariants invariants)*)
ty_own (Frac 1%Qp) l ={⊤}=∗ ty_own Own l;
Fractional (λ q, ty_own (Frac q) l)

Conceptually this seems like the right thing but the splitting of the fractional when combined by the
viewshift and laters causes big problems. Especially it does not seem clear how to define the guarded
type such that it fulfills all the axioms:
guarded ty:
 Own: ▷ l ◁ₗ{Own} ty
 -> does not work because we don't have the viewshift for the frac to own direction

 β: ▷ |={⊤}=> l ◁ₗ{β} ty
 -> does not work because we cannot prove one direction of the Fractional:
 ▷ |={⊤}=> l ◁ₗ{Frac q + p} ty -∗ (▷ |={⊤}=> l ◁ₗ{Frac q} ty) ∗ (▷ |={⊤}=> l ◁ₗ{Frac p} ty)
 -> we don't have a viewshift after stripping the later
 -> a viewshift instead of the entailment does not help either as it does not commute with the later

Only fractional references:
Definition own_state : Type := Qp.
Definition own : own_state := 1%Qp.
Fractional (λ q, ty_own q l)

guarded ty: ▷ l ◁ₗ{q} ty -> should work since ∗ commutes with ▷ in both directions
Lock: exists i, l meta is i and cinv_own i q and inv lock ...

Problem: Lock would not be movable (cannot get the pointsto out without aa viewshift)
Maybe we could add a viewshift when going from own to own val or back
but might not be such a big problem since one could transform it into a movable lock with one step


Other problem with all the Fractional based approaches: you ahve to merge existential quantifiers, which
can come from e.g. refinements.

The right lemma which you want to prove seems to be
∀ q1 q2 x y, P q1 x -∗ P q2 y -∗ P q1 x ∗ P q2 x
This should be provable for most types (e.g. optional assuming l◁ₗ{β} ty -∗ l◁ₗ{β} optty -∗ False)
and it should commute with separating conjuction (necessary for e.g. struct )

We will also probably need a meta like thing in heap lang to associate gnames with locations to ensure that things agree (e.g. gnames used in cancellable invariants lock).

See also http://www0.cs.ucl.ac.uk/staff/J.Brotherston/CAV20/SL_hybrid_perms.pdf



Insight: All approaches above are probably doomed.
Notes:
An additional parameter to shared references is necessary to ensure that you only try to merge related fractions (similar to lifetimes).

This parameter can be used to fix existential quantifiers and the choice inside option. These won't be able to be changed when shared (but when owned).

Owned to shared is a viewshift which creates the value of this parameter.

Question: what should the type of this parameter be? The easiest would be if it is defined by the type but that would probably break fixpoints.
Other option: gname
Other option: Something more complicated like lifetime

Maybe merging and splitting fractions will need a step
We will need an additional parameter

 *)

Definition adr2val (l : address) := Vptr l.1 (Ptrofs.repr l.2).
Coercion adr2val : address >-> val.

(* overwrites res_predicates.val2address; unsgined seem to make more sense *)
Definition val2adr (v: val) : option address := 
  match v with Vptr b ofs => Some (b, Ptrofs.unsigned ofs) | _ => None end.
  
(* Ptrofs.intval Ptrofs.repr *)
Definition norm_adr (l:address) : address := (l.1, (Ptrofs.unsigned $ Ptrofs.repr l.2)).

Lemma val2adr2val_id l : val2adr $ adr2val (norm_adr l) = Some $ norm_adr l.
Proof.
  destruct l; try done.
  rewrite  /norm_adr /= Ptrofs.unsigned_repr //.
  rep_lia.
Qed.


Definition shrN : namespace := nroot.@"shrN".
Definition mtN : namespace := nroot.@"mtN".
Definition mtE : coPset := ↑mtN.
Inductive own_state : Type :=
| Own | Shr.
Definition own_state_min (β1 β2 : own_state) : own_state :=
  match β1 with
  | Own => β2
  | _ => Shr
  end.
(* Should this be lower (e.g., no type and memval, and a single ↦ instead of mapsto)? *)
Definition heap_mapsto_own_state `{!typeG Σ} (t : type) (l : address) (β : own_state) (v : val) : iProp Σ :=
  match β with
  | Own => mapsto Tsh t l v
  | Shr => inv mtN (∃ q, mapsto q t l v)
  end.
Notation "l ↦_ t [ β ] v" := (heap_mapsto_own_state t l β v)
  (at level 20, t at level 0, β at level 50, format "l  ↦_ t [ β ]  v") : bi_scope.
Definition heap_mapsto_own_state_type `{!typeG Σ} (t : type) (l : address) (β : own_state) : iProp Σ :=
  (∃ v, l ↦_t[β] v).
Notation "l ↦[ β ]| t |" := (heap_mapsto_own_state_type t l β)
  (at level 20, β at level 50, format "l  ↦[ β ]| t |") : bi_scope.

Section own_state.
  Context `{!typeG Σ}.
  Global Instance own_state_min_left_id : LeftId (=) Own own_state_min.
  Proof. by move => []. Qed.
  Global Instance own_state_min_right_id : RightId (=) Own own_state_min.
  Proof. by move => []. Qed.

  Global Instance heap_mapsto_own_state_shr_persistent t l v : Persistent (l ↦_t[ Shr ] v).
  Proof. apply _. Qed.

(* Caesium uses a ghost heap to track the bounds of each allocation (block) persistently.
   We don't have anything analogous; when it would be required, we use valid_pointer, but
   that's not a persistent assertion and actually owns part of the memory. *)

(*  Lemma heap_mapsto_own_state_loc_in_bounds l β v :
    l ↦[β] v ⊢ loc_in_bounds l (length v).
  Proof.
    destruct β; last by iIntros "[$ _]".
    iIntros "Hl". by iApply heap_mapsto_loc_in_bounds.
  Qed.*)

(*  Lemma heap_mapsto_own_state_nil l β:
    l ↦[β] [] ⊣⊢ loc_in_bounds l 0.
  Proof. destruct β; [ by apply heap_mapsto_nil | by rewrite /= right_id ]. Qed.*)

  Lemma heap_mapsto_own_state_to_mt t l v E β:
    ↑mtN ⊆ E → l ↦_t[β] v ={E}=∗ ∃ q, ⌜β = Own → q = Tsh⌝ ∗ mapsto q t l v.
  Proof.
    iIntros (?) "Hl".
    destruct β; simpl; eauto with iFrame.
    iInv "Hl" as ">H". iDestruct "H" as (q) "H".
    pose proof (slice.cleave_join q) as Hq.
    rewrite -mapsto_share_join //.
    iDestruct "H" as "(H1 & H2)"; iSplitL "H1"; iExists _; by iFrame.
  Qed.

  Lemma heap_mapsto_own_state_from_mt t (l : address) v E β q:
    (β = Own → q = Tsh) → mapsto q t l v ={E}=∗ l ↦_t[β] v.
  Proof.
    iIntros (Hb) "Hl" => /=.
    destruct β => /=; first by rewrite Hb.
    iApply inv_alloc. iModIntro. iExists _. iFrame.
  Qed.

(*  Lemma heap_mapsto_own_state_alloc l β v :
    length v ≠ 0%nat →
    l ↦[β] v -∗ alloc_alive_loc l.
  Proof.
    iIntros (?) "Hl".
    destruct β; [ by iApply heap_mapsto_alive|].
    iApply heap_mapsto_alive_strong.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (? ?) "?"; [done|].
    iApply fupd_mask_intro; [done|]. iIntros "_". iExists _, _. by iFrame.
  Qed.*)

  Lemma heap_mapsto_own_state_share t l v E:
    l ↦_t[Own] v ={E}=∗ l ↦_t[Shr] v.
  Proof. by apply heap_mapsto_own_state_from_mt. Qed.

  Lemma heap_mapsto_own_state_exist_share t l E:
    l ↦[Own]|t| ={E}=∗ l ↦[Shr]|t|.
  Proof.
    iDestruct 1 as (v) "Hl". iMod (heap_mapsto_own_state_share with "Hl").
    iExists _. by iFrame.
  Qed.

(*  Lemma heap_mapsto_own_state_app l v1 v2 β:
    l ↦[β] (v1 ++ v2) ⊣⊢ l ↦[β] v1 ∗ (adr_add l (length v1)) ↦[β] v2.
  Proof.
    destruct β; rewrite /= ?heap_mapsto_app //.
    - rewrite big_sepL_app. app_length -loc_in_bounds_split.
    setoid_rewrite shift_loc_assoc_nat.
    iSplit; iIntros "[[??][??]]"; iFrame.
  Qed.

  Lemma heap_mapsto_own_state_layout_alt l β ly:
    l ↦[β]|ly| ⊣⊢ ⌜l `has_layout_loc` ly⌝ ∗ ∃ v, ⌜v `has_layout_val` ly⌝ ∗ l↦[β] v.
  Proof. iSplit; iDestruct 1 as (???) "?"; eauto with iFrame. iExists _. by iFrame. Qed.*)
End own_state.
Arguments heap_mapsto_own_state : simpl never.

(* Not sure what the equivalent to memcast is in VST. *)
(** [memcast_compat_type] describes how a type can transfered via a
mem_cast (see also [ty_memcast_compat] below):
- MCNone: The type cannot be transferred across a mem_cast.
- MCCopy: The value type can be transferred to a mem_casted value.
- MCId: mem_cast on a value of this type is the identity.

MCId implies the other two and MCCopy implies MCNone.
  *)
Inductive memcast_compat_type : Set :=
| MCNone | MCCopy | MCId.


Local Open Scope Z.
Section CompatRefinedC.
  Context `{!typeG Σ} {cs : compspecs}.

  (* refinedC only checks if `v` fits in the size of ot *)
  Definition has_layout_val (v:val) (ot:Ctypes.type) : Prop := tc_val' ot v.
  Arguments has_layout_val : simpl never.

  Global Typeclasses Opaque has_layout_val.
    
  (*  NOTE maybe change this with field_compatible? *)
  Definition has_layout_loc (l:address) (ot:Ctypes.type) : Prop :=
    field_compatible ot [] (adr2val l).

  Arguments has_layout_loc : simpl never.
  Global Typeclasses Opaque has_layout_loc.

  Definition mapsto (l : address) (q : Share.t) (ot : Ctypes.type) (v : val) : mpred := mapsto q ot l v.

  (* TODO maybe use `mapsto_` ?*)
  Definition mapsto_layout (l : address) (q : Share.t) (ot : Ctypes.type) : mpred :=
    (∃ v,  <affine>⌜has_layout_val v ot⌝ ∗ <affine>⌜has_layout_loc l ot⌝ ∗ mapsto l q ot v).
  Definition mapsto_layout_ (l : address) (q : Share.t) (ot : Ctypes.type) : mpred :=
    (∃ v, mapsto l q ot v).
  
  (* Ke: refinedC does not have this; is our maspto too strong? *)
  Lemma maptso_has_layout_val l q ot (v:val) :
    mapsto l q ot v ⊢ ⌜has_layout_val v ot⌝.
  Proof.
    unfold mapsto, mapsto_memory_block.mapsto.
    iIntros "H".
    destruct (access_mode ot) eqn:Hot; try done.
    destruct (type_is_volatile ot) eqn:Hotv; try done.
    destruct l eqn:Hl; try done.
    destruct (readable_share_dec q) eqn:Hq; unfold has_layout_val, tc_val'.
    - rewrite bi.pure_impl.  iIntros "%". iDestruct "H" as "[[$ _]|[% _]]". done.
    - iDestruct "H" as "[[$ _] _]".
  Qed.

  (* Lemma maptso_layout_has_layout_loc (l:address) q ot (v:val) :
    mapsto l q ot v ⊢ ⌜has_layout_loc l ot⌝.
  Proof.
    unfold mapsto, mapsto_memory_block.mapsto, has_layout_loc.
    iIntros "H".
    destruct (access_mode ot) eqn:Hot; try done.
    destruct (type_is_volatile ot) eqn:Hotv; try done.
    destruct (adr2val l) eqn:Hl; try done.
    destruct (readable_share_dec q) eqn:Hq.
    - iDestruct "H" as "[[% H]|[% H]]".
      + Search field_compatible mapsto_memory_block.mapsto .
         unfold address_mapsto.
        inv Hl.
        iDestruct "H" as (ms) "((% & % & %) & ?)".
        unfold field_compatible.
      + unfold address_mapsto.
        inv Hl.
        iDestruct "H" as (??) "((% & % & $) & ?)".  
    -  iDestruct "H" as "[[_ %] _]"; iPureIntro.
       inv Hl.
       done.
  Qed. *)

  (* Lemma mapsto_layout_equiv l q ot :
    mapsto_layout l q ot ⊣⊢ mapsto_layout_ l q ot.
  Proof.
    rewrite /mapsto_layout /mapsto_layout_.
    apply bi.equiv_entails_2; apply bi.exist_mono => v.
    - iIntros "(? & ? & $)".
    - iIntros "H".
      iSplit. { rewrite maptso_layout_has_layout_val //. iDestruct "H" as "%". iPureIntro; done. }
      iSplit. { rewrite maptso_layout_has_layout_loc //. iDestruct "H" as "%". iPureIntro; done. }
      done.
  Qed. *)

End CompatRefinedC.

Notation "v `has_layout_val` ot" := (has_layout_val v ot) (at level 50) : stdpp_scope.
Notation "l `has_layout_loc` ot" := (has_layout_loc l ot) (at level 50) : stdpp_scope.
Notation "l ↦{ sh '}' '|' ot '|' v" := (mapsto l sh ot v)
  (at level 20, sh at level 50, format "l ↦{ sh '}' '|' ot '|' v") : bi_scope.
Notation "l ↦| ot | v" := (mapsto l Tsh ot v)
  (at level 20, format "l  ↦| ot | v") : bi_scope.
Notation "l ↦{ sh '}' '|' ot '|' '_'" := (mapsto_layout l sh ot)
  (at level 20, sh at level 50, format "l ↦{ sh '}' '|' ot '|' _") : bi_scope.
Notation "l ↦| ot '|' '-'" := (mapsto_layout l Tsh ot)
  (at level 20, format "l ↦| ot '|' '-'") : bi_scope.

(* In Caesium, all values are lists of bytes in memory, and structured data is just an
   assertion on top of that. What do we want the values that appear in our types to be? *)
Record type `{!typeG Σ} {cs : compspecs} := {
  (** [ty_has_op_type ot mt] describes in which cases [l ◁ₗ ty] can be
      turned into [∃ v. l ↦ v ∗ v ◁ᵥ ty]. The op_type [ot] gives the
      requested layout for the location and [mt] describes how the
      value of [v ◁ᵥ ty] is changed by a memcast (i.e. when read from
      memory). [ty_has_op_type] should be written such that it
      computes well and can be solved by [done]. Also [ty_has_op_type]
      should be defined for [UntypedOp]. *)
  (* TODO: add
   ty_has_op_type ot mt → ty_has_op_type (UntypedOp (ot_layout ot)) mt
   This property is never used explicitly, but relied on by some typing rules *)
  ty_has_op_type : Ctypes.type → memcast_compat_type → Prop;
  (** [ty_own β l ty], also [l ◁ₗ{β} ty], states that the location [l]
  has type [ty]. [β] determines whether the location is fully owned
  [Own] or shared [Shr] (shared is mainly used for global variables). *)
  ty_own : own_state → address → iProp Σ;
  (** [ty_own v ty], also [v ◁ᵥ ty], states that the value [v] has type [ty]. *)
  ty_own_val : val → iProp Σ;
  (** [ty_share] states that full ownership can always be turned into shared ownership. *)
  ty_share l E : ↑shrN ⊆ E → ty_own Own l ={E}=∗ ty_own Shr l;
  (** [ty_shr_pers] states that shared ownership is persistent. *)
  ty_shr_pers l : Persistent (ty_own Shr l);
  (** [ty_aligned] states that from [l ◁ₗ{β} ty] follows that [l] is
  aligned according to [ty_has_op_type]. *)
  ty_aligned ot mt l : ty_has_op_type ot mt → ty_own Own l -∗ <absorb> ⌜l `has_layout_loc` ot⌝;
  (** [ty_size_eq] states that from [v ◁ᵥ ty] follows that [v] has a
  size according to [ty_has_op_type]. *)
  ty_size_eq ot mt v : ty_has_op_type ot mt → ty_own_val v -∗ <absorb> ⌜v `has_layout_val` ot⌝;
  (** [ty_deref] states that [l ◁ₗ ty] can be turned into [v ◁ᵥ ty] and a points-to
  according to [ty_has_op_type]. *)
  ty_deref ot mt l : ty_has_op_type ot mt → ty_own Own l -∗ ∃ v, mapsto l Tsh ot v ∗ ty_own_val v;
  (** [ty_ref] states that [v ◁ₗ ty] and a points-to for a suitable location [l ◁ₗ ty]
  according to [ty_has_op_type]. *)
  ty_ref ot mt (l : address) v : ty_has_op_type ot mt → <affine> ⌜l `has_layout_loc` ot⌝ -∗ mapsto l Tsh ot v -∗ ty_own_val v -∗ ty_own Own l;
  (** [ty_memcast_compat] describes how a value of type [ty] is
  transformed by memcast. [MCNone] means there is no information about
  the new value, [MCCopy] means the value can change, but it still has
  type [ty], and [MCId] means the value does not change. *)
(*  ty_memcast_compat v ot mt st:
    ty_has_op_type ot mt →
    (* TODO: Should this be a -∗ for consistency with the other properties?
    We currently use ⊢ because it makes applying some lemmas easier. *)
    ty_own_val v ⊢
    match mt with
    | MCNone => True
    | MCCopy => ty_own_val (mem_cast v ot st)
    | MCId => ⌜mem_cast_id v ot⌝ (* This could be tc_val' ot v *)
    end;*)
}.
Arguments ty_own : simpl never.
Arguments ty_has_op_type {_ _ _} _.
Arguments ty_own_val {_ _ _} _ : simpl never.
Global Existing Instance ty_shr_pers.

(*Section memcast.
  Context `{!typeG Σ}.

  Lemma ty_memcast_compat_copy v ot ty st:
    ty.(ty_has_op_type) ot MCCopy →
    ty.(ty_own_val) v ⊢ ty.(ty_own_val) (mem_cast v ot st).
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCCopy). Qed.

  Lemma ty_memcast_compat_id v ot ty:
    ty.(ty_has_op_type) ot MCId →
    ty.(ty_own_val) v ⊢ ⌜mem_cast_id v ot⌝.
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCId inhabitant). Qed.

  Lemma mem_cast_compat_id (P : val → iProp Σ) v ot st mt:
    (P v ⊢ ⌜mem_cast_id v ot⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof. iIntros (HP) "HP". iDestruct (HP with "HP") as %Hm. rewrite Hm. by destruct mt. Qed.

  Lemma mem_cast_compat_Untyped (P : val → iProp Σ) v ot st mt:
    ((if ot is UntypedOp _ then False else True) → P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end) →
    P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end.
  Proof. move => Hot. destruct ot; try by apply: Hot. apply: mem_cast_compat_id. by iIntros "?". Qed.

  (* It is important this this computes well so that it can be solved automatically. *)
  Definition is_int_ot (ot : op_type) (it : int_type) : Prop:=
    match ot with | IntOp it' => it = it' | UntypedOp ly => ly = it_layout it | _ => False end.
  Definition is_ptr_ot (ot : op_type) : Prop:=
    match ot with | PtrOp => True | UntypedOp ly => ly = void* | _ => False end.
  Definition is_value_ot (ot : op_type) (ot' : op_type) :=
    if ot' is UntypedOp ly then ly = ot_layout ot else ot' = ot.

  Lemma is_int_ot_layout it ot:
    is_int_ot ot it → ot_layout ot = it.
  Proof. by destruct ot => //= ->. Qed.

  Lemma is_ptr_ot_layout ot:
    is_ptr_ot ot → ot_layout ot = void*.
  Proof. by destruct ot => //= ->. Qed.

  Lemma is_value_ot_layout ot ot':
    is_value_ot ot ot' → ot_layout ot' = ot_layout ot.
  Proof. by destruct ot' => //= <-. Qed.

  Lemma mem_cast_compat_int (P : val → iProp Σ) v ot st mt it:
    is_int_ot ot it →
    (P v ⊢ ⌜∃ z, val_to_Z v it = Some z⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof.
    move => ? HT. apply: mem_cast_compat_Untyped => ?.
    apply: mem_cast_compat_id. destruct ot => //; simplify_eq/=.
    etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_int.
  Qed.

  Lemma mem_cast_compat_loc (P : val → iProp Σ) v ot st mt:
    is_ptr_ot ot →
    (P v ⊢ ⌜∃ l, v = val_of_loc l⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof.
    move => ? HT. apply: mem_cast_compat_Untyped => ?.
    apply: mem_cast_compat_id. destruct ot => //; simplify_eq/=.
    etrans; [done|]. iPureIntro => -[? ->]. by apply: mem_cast_id_loc.
  Qed.
End memcast.*)

Class Copyable `{!typeG Σ} {cs : compspecs} (ty : type) := {
  copy_own_persistent v : Persistent (ty.(ty_own_val) v);
  copy_own_affine v : Affine (ty.(ty_own_val) v);
  copy_shr_acc E ot l :
    mtE ⊆ E → ty.(ty_has_op_type) ot MCCopy →
    ty.(ty_own) Shr l ={E}=∗ <affine> ⌜l `has_layout_loc` ot⌝ ∗
       (* TODO: the closing conjuct does not make much sense with True *)
       ∃ q' vl, mapsto l q' ot vl ∗ ▷ ty.(ty_own_val) vl ∗ (▷mapsto l q' ot vl ={E}=∗ True)
}.
Global Existing Instance copy_own_persistent.
Global Existing Instance copy_own_affine.

(*Class LocInBounds `{!typeG Σ} (ty : type) (β : own_state) (n : nat) := {
  loc_in_bounds_in_bounds l : ty.(ty_own) β l -∗ loc_in_bounds l n
}.
Arguments loc_in_bounds_in_bounds {_ _} _ _ _ {_} _.
Global Hint Mode LocInBounds + + + + - : typeclass_instances.

Section loc_in_bounds.
  Context `{!typeG Σ}.

  Lemma movable_loc_in_bounds ty l ot mt:
    ty.(ty_has_op_type) ot mt →
    ty.(ty_own) Own l -∗ loc_in_bounds l (ly_size (ot_layout ot)).
  Proof.
    iIntros (?) "Hl". iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %<-; [done|]. by iApply heap_mapsto_loc_in_bounds.
  Qed.

  Global Instance intro_persistent_loc_in_bounds l n:
    IntroPersistent (loc_in_bounds l n) (loc_in_bounds l n).
  Proof. constructor. by iIntros "#H !>". Qed.
End loc_in_bounds.

Class AllocAlive `{!typeG Σ} (ty : type) (β : own_state) (P : iProp Σ) := {
  alloc_alive_alive l : P -∗ ty.(ty_own) β l -∗ alloc_alive_loc l
}.
Arguments alloc_alive_alive {_ _} _ _ _ {_} _.
Global Hint Mode AllocAlive + + + + - : typeclass_instances.

Definition type_alive `{!typeG Σ} (ty : type) (β : own_state) : iProp Σ :=
  □ (∀ l, ty.(ty_own) β l -∗ alloc_alive_loc l).
Notation type_alive_own ty := (type_alive ty Own).

Section alloc_alive.
  Context `{!typeG Σ}.

  Lemma movable_alloc_alive ty l ot mt :
    (ot_layout ot).(ly_size) ≠ 0%nat →
    ty.(ty_has_op_type) ot mt →
    ty.(ty_own) Own l -∗ alloc_alive_loc l.
  Proof.
    iIntros (??) "Hl". iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %Hv; [done|].
    iApply heap_mapsto_alive => //. by rewrite Hv.
  Qed.

  Global Instance intro_persistent_alloc_global l:
    IntroPersistent (alloc_global l) (alloc_global l).
  Proof. constructor. by iIntros "#H !>". Qed.

  Global Instance intro_persistent_type_alive ty β:
    IntroPersistent (type_alive ty β) (type_alive ty β).
  Proof. constructor. by iIntros "#H !>". Qed.

  Global Instance AllocAlive_simpl_and ty β P P' `{!AllocAlive ty β P'} `{!IsEx P} :
    SimplAndUnsafe (AllocAlive ty β P) (P = P').
  Proof. by move => ->. Qed.
End alloc_alive.

Global Typeclasses Opaque type_alive.*)

Notation "l ◁ₗ{ β } ty" := (ty_own ty β l) (at level 15, format "l  ◁ₗ{ β }  ty") : bi_scope.
Notation "l ◁ₗ ty" := (ty_own ty Own l) (at level 15) : bi_scope.
Notation "v ◁ᵥ ty" := (ty_own_val ty v) (at level 15) : bi_scope.

Declare Scope printing_sugar.
Notation "'frac' { β } l ∶ ty" := (ty_own ty β l) (at level 100, only printing) : printing_sugar.
Notation "'own' l ∶ ty" := (ty_own ty Own l) (at level 100, only printing) : printing_sugar.
Notation "'shr' l ∶ ty" := (ty_own ty Shr l) (at level 100, only printing) : printing_sugar.
Notation "v ∶ ty" := (ty_own_val ty v) (at level 200, only printing) : printing_sugar.

(*** tytrue *)
Section true.
  Context `{!typeG Σ} {cs : compspecs}.
  (** tytrue is a dummy type that all values and locations have. *)
  Program Definition tytrue : type := {|
    ty_own _ _ := True%I;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := emp;
  |}.
  Solve Obligations with try done.
  Next Obligation. iIntros (???) "?". done. Qed.
End true.
Global Instance inhabited_type `{!typeG Σ} {cs : compspecs} : Inhabited type := populate tytrue.
(* tytrue is not opaque because we don't have typing rules for it. *)
(* Global Typeclasses Opaque tytrue. *)

(*** refinement types *)
Record rtype `{!typeG Σ} {cs : compspecs} (A : Type) := RType {
  rty : A → type;
}.
Arguments RType {_ _ _ _} _.
Arguments rty {_ _ _ _} _.
Add Printing Constructor rtype.

Bind Scope bi_scope with type.
Bind Scope bi_scope with rtype.

Definition with_refinement `{!typeG Σ} {cs : compspecs} {A} (r : rtype A) (x : A) : type := r.(rty) x.
Notation "x @ r" := (with_refinement r x) (at level 14) : bi_scope.
Arguments with_refinement : simpl never.

Program Definition ty_of_rty `{!typeG Σ} {cs : compspecs} {A} (r : rtype A) : type := {|
  ty_own q l := (∃ x, (x @ r).(ty_own) q l)%I;
  ty_has_op_type ot mt := forall x, (x @ r).(ty_has_op_type) ot mt;
  ty_own_val v := (∃ x, (x @ r).(ty_own_val) v)%I;
|}.
Next Obligation. iDestruct 1 as (?) "H". iExists _. by iMod (ty_share with "H") as "$". Qed.
Next Obligation.
  iIntros (Σ ?? A r β mt l Hly). iDestruct 1 as (x) "Hv". by iDestruct (ty_aligned with "Hv") as %Hv; [done|].
Qed.
Next Obligation.
  iIntros (Σ ?? A r ot mt v Hly). iDestruct 1 as (x) "Hv". 
 by iDestruct (ty_size_eq with "Hv") as %Hv.
Qed.
Next Obligation.
  iIntros (Σ ?? A r ot mt l Hly). iDestruct 1 as (x) "Hl".
  iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
  eauto with iFrame.
Qed.
Next Obligation.
  iIntros (Σ ?? A r ot mt l v Hly ?) "Hl". iDestruct 1 as (x) "Hv".
  iDestruct (ty_ref with "[] Hl Hv") as "Hl"; [done..|].
  iExists _. iFrame.
Qed.
(*Next Obligation.
  iIntros (Σ ?? A r v ot mt st Hot) "[%x Hv]".
  iDestruct (ty_memcast_compat with "Hv") as "?"; [done|].
  case_match => //. iExists _. iFrame.
Qed.*)

Coercion ty_of_rty : rtype >-> type.
(* TODO: somehow this instance does not work*)
(* Global Instance assume_inj_with_refinement `{!typeG Σ} ty : AssumeInj (=) (=) (with_refinement ty). *)
(* Proof. done. Qed. *)

(* TODO: remove the following? *)
(* Record refined `{!typeG Σ} := { *)
(*   r_type : Type; *)
(*   r_rty : rtype; *)
(*   r_fn : r_type → r_rty.(rty_type); *)
(* }. *)
(* Program Definition rty_of_refined `{!typeG Σ} (r : refined) : rtype := {| *)
(*   rty_type := r.(r_type); *)
(*   rty x := r.(r_rty).(rty) (r.(r_fn) x) *)
(* |}. *)
(* Coercion rty_of_refined : refined >-> rtype. *)

Section rmovable.
  Context `{!typeG Σ} {cs : compspecs}.

  Global Program Instance copyable_ty_of_rty A r `{!∀ x : A, Copyable (x @ r)} : Copyable r.
  Next Obligation.
    iIntros (A r ? E ly l ??). iDestruct 1 as (x) "Hl".
    iMod (copy_shr_acc with "Hl") as (? q' vl) "(?&?&?)" => //.
    iSplitR => //. iExists _, _. iFrame. auto.
  Qed.
End rmovable.

Notation "l `at_type` ty" := (with_refinement ty <$> l) (at level 50) : bi_scope.
(* Must be an Hint Extern instead of an Instance since simple apply is not able to apply the instance. *)
Global Hint Extern 1 (AssumeInj (=) (=) (with_refinement _)) => exact: I : typeclass_instances.

(*** Monotonicity *)
Section mono.
  Context `{!typeG Σ} {cs : compspecs}.

  Inductive type_le' (ty1 ty2 : type) : Prop :=
    Type_le :
      (* We omit [ty_has_op_type] on purpose as it is not preserved by fixpoints. *)
      (∀ β l, ty1.(ty_own) β l ⊢ ty2.(ty_own) β l) →
      (∀ v, ty1.(ty_own_val) v ⊢ ty2.(ty_own_val) v) →
      type_le' ty1 ty2.
  Global Instance type_le : SqSubsetEq type := type_le'.

  Inductive type_equiv' (ty1 ty2 : type) : Prop :=
    Type_equiv :
      (* We omit [ty_has_op_type] on purpose as it is not preserved by fixpoints. *)
      (∀ β l, ty1.(ty_own) β l ≡ ty2.(ty_own) β l) →
      (∀ v, ty1.(ty_own_val) v ≡ ty2.(ty_own_val) v) →
      type_equiv' ty1 ty2.
  Global Instance type_equiv : Equiv type := type_equiv'.

  Global Instance type_equiv_antisym :
    AntiSymm (≡@{type} ) (⊑).
  Proof. move => ?? [??] [??]. split; intros; by apply (anti_symm (⊢)). Qed.

  Global Instance type_le_preorder : PreOrder (⊑@{type} ).
  Proof.
    constructor.
    - done.
    - move => ??? [??] [??].
      constructor => *; (etrans; [match goal with | H : _ |- _ => apply H end|]; done).
  Qed.

  Global Instance type_equivalence : Equivalence (≡@{type} ).
  Proof.
    constructor.
    - done.
    - move => ?? [??]. constructor => *; by symmetry.
    - move => ??? [??] [??].
      constructor => *; (etrans; [match goal with | H : _ |- _ => apply H end|]; done).
  Qed.

  Global Instance ty_le_proper : Proper ((≡) ==> (≡) ==> iff) (⊑@{type} ).
  Proof.
    move => ?? [Hl1 Hv1] ?? [Hl2 Hv2].
    split; move => [??]; constructor; intros.
    - by rewrite -Hl1 -Hl2.
    - by rewrite -Hv1 -Hv2.
    - by rewrite Hl1 Hl2.
    - by rewrite Hv1 Hv2.
  Qed.

  Lemma type_le_equiv_list (f : list type → type) :
    Proper (Forall2 (⊑) ==> (⊑)) f →
    Proper (Forall2 (≡) ==> (≡)) f.
  Proof.
    move => HP ?? Heq. apply (anti_symm (⊑)); apply HP.
    2: symmetry in Heq.
    all: by apply: Forall2_impl; [done|] => ?? ->.
  Qed.

  Global Instance ty_own_le : Proper ((⊑) ==> eq ==> eq ==> (⊢)) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Lemma ty_own_entails `{!typeG Σ} ty1 ty2 β l:
    ty1 ≡@{type} ty2 →
    ty_own ty1 β l ⊢ ty_own ty2 β l.
  Proof. by move => [-> ?]. Qed.

  Global Instance ty_own_val_le : Proper ((⊑) ==> eq ==> (⊢)) ty_own_val.
  Proof. intros ?? EQ ??->. apply EQ. Qed.
  Global Instance ty_own_val_proper : Proper ((≡) ==> eq ==> (≡)) ty_own_val.
  Proof. intros ?? EQ ??->. apply EQ. Qed.

  Lemma ty_of_rty_le A rty1 rty2 :
    (∀ x : A, (x @ rty1)%I ⊑ (x @ rty2)%I) →
    ty_of_rty rty1 ⊑ ty_of_rty rty2.
  Proof.
    destruct rty1, rty2; simpl in *. rewrite /with_refinement/=.
    move => Hle. constructor => /=.
    - move => ??. rewrite /ty_own/=. f_equiv => ?. apply Hle.
    - move => ?. rewrite /ty_own_val/=. f_equiv => ?. apply Hle.
  Qed.
  Lemma ty_of_rty_proper A rty1 rty2 :
    (∀ x : A, (x @ rty1)%I ≡ (x @ rty2)%I) →
    ty_of_rty rty1 ≡ ty_of_rty rty2.
  Proof.
    destruct rty1, rty2; simpl in *. rewrite /with_refinement/=.
    move => Heq. constructor => /=.
    - move => ??. rewrite /ty_own/=. f_equiv => ?. apply Heq.
    - move => ?. rewrite /ty_own_val/=. f_equiv => ?. apply Heq.
  Qed.
End mono.

Notation TypeMono T := (Proper (pointwise_relation _ (⊑) ==> pointwise_relation _ (⊑)) T).

Global Typeclasses Opaque ty_own ty_own_val ty_of_rty with_refinement.

Ltac simpl_type :=
  simpl;
  repeat match goal with
        | |- context C [ty_own {| ty_own := ?f |}] => let G := context C [f] in change G
        | |- context C [ty_own_val {| ty_own_val := ?f |}] => let G := context C [f] in change G
        | |- context C [ty_own (?x @ {| rty := ?f |} )] =>
            let G := context C [let '({| ty_own := y |} ) := (f x) in y ] in
            change G
        | |- context C [ty_own_val (?x @ {| rty := ?f |} )] =>
            let G := context C [let '({| ty_own_val := y |} ) := (f x) in y ] in
            change G
     end; simpl.

Ltac unfold_type_equiv :=
  lazymatch goal with
  | |- Forall2 _ (_ <$> _) (_ <$> _) => apply list_fmap_Forall2_proper
  | |- (?a @ ?ty1)%I ⊑ (?b @ ?ty2)%I => change (rty ty1 a ⊑ rty ty2 b); simpl
  | |- (?a @ ?ty1)%I ≡ (?b @ ?ty2)%I => change (rty ty1 a ≡ rty ty2 b); simpl
  | |- ty_of_rty _ ⊑ ty_of_rty _ => simple refine (ty_of_rty_le _ _ _ _) => ? /=
  | |- ty_of_rty _ ≡ ty_of_rty _ => simple refine (ty_of_rty_proper _ _ _ _) => ? /=
  | |- {| ty_own := _ |} ⊑ {| ty_own := _ |} =>
      constructor => *; simpl_type
  | |- {| ty_own := _ |} ≡ {| ty_own := _ |} =>
      constructor => *; simpl_type
  | |- context [let '_ := ?x in _] => destruct x
  end.

(* A version of f_equiv which performs better for the kinds of goals
we see in this development (e.g. mpool_spec). *)
Ltac f_equiv' :=
  match goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- prod_relation _ _ ?p _ => is_var p; destruct p
  (* We support matches on both sides, *if* they concern the same variable, or *)
     (* variables in some relation. *)
  | |- ?R (match ?x with _ => _ end) (match ?x with _ => _ end) =>
    destruct x
  | H : ?R ?x ?y |- ?R2 (match ?x with _ => _ end) (match ?y with _ => _ end) =>
     destruct H
  | |- _ = _ => reflexivity

  | |- ?R (?f _) _ => simple apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  (* In case the function symbol differs, but the arguments are the same, *)
     (* maybe we have a pointwise_relation in our context. *)
  (* TODO: If only some of the arguments are the same, we could also *)
  (*    query for "pointwise_relation"'s. But that leads to a combinatorial *)
  (*    explosion about which arguments are and which are not the same. *)
  | H : pointwise_relation _ ?R ?f ?g |- ?R (?f ?x) (?g ?x) => simple apply H
  | H : pointwise_relation _ (pointwise_relation _ ?R) ?f ?g |- ?R (?f ?x ?y) (?g ?x ?y) => simple apply H
  end.

Ltac solve_type_proper :=
  solve_proper_core ltac:(fun _ => first [ fast_reflexivity | unfold_type_equiv | f_contractive | f_equiv' | reflexivity ]).
(* for debugging use
   solve_proper_prepare.
   first [ eassumption | fast_reflexivity | unfold_type_equiv | f_contractive | f_equiv' | reflexivity ].
*)


(*** Tests *)
Section tests.
  Context `{!typeG Σ} {cs : compspecs}.

  Example binding l (r : Z → rtype N) v x T : True -∗ l ◁ₗ x @ r v ∗ T. Abort.

End tests.
