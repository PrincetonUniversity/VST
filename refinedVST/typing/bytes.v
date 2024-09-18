From VST.typing Require Export type.
From VST.typing Require Import programs int own.
From VST.typing Require Import type_options.

(* NOTE: we might want to have a type [bytes : list mbyte → type] one day,
and the [bytewise] abstraction could be encoded on top of it. *)

Section bytewise.
  Context `{!typeG Σ} {cs : compspecs}.
  Implicit Types P : memval → Prop.

  (* Because ty_own_val is at the val level, for now this is defined only for bytewise representations
     of vals, rather than arbitrary byte arrays that happen to have the right layout. *)

  Program Definition bytewise (P : memval → Prop) (ly : Ctypes.type) : type := {|
    ty_has_op_type ot mt := ot = ly;
    (* Does bytewise make sense for non-by-value types? Structs do have
       defined layouts in memory, but we don't have a function for interpreting memvals as structs.
       We could consider lifting the definition of ↦[β] all the way to data_at? *)
    ty_own β l :=
      ∃ v, <affine> ⌜field_compatible ly [] l⌝ ∗
           <affine> ⌜∃ ch bl, access_mode ly = By_value ch ∧ encode_val ch v = bl ∧ Forall P bl⌝ ∗
           l ↦_ly[β] v;
    ty_own_val v := (<affine> ⌜∃ ch bl, access_mode ly = By_value ch ∧ encode_val ch v = bl ∧ Forall P bl⌝)%I;
  |}%I.
  Next Obligation.
    iIntros (?????). iDestruct 1 as (?) "(?&?&Hl)".
    iMod (heap_mapsto_own_state_share with "Hl") as "Hl".
    eauto with iFrame.
  Qed.
  Next Obligation. iIntros (?????->). by iDestruct 1 as (???) "_". Qed.
  Next Obligation. Admitted.
(*   Next Obligation. by iIntros (?????-> [??]). Qed. *)
  Next Obligation. iIntros (?????->). iDestruct 1 as (???) "?". by eauto. Qed.
  Next Obligation. iIntros (????? v -> ?) "? [%%]". iExists v. iFrame. eauto. Qed.
(*   Next Obligation. iIntros (ly P v ot mt st ?). apply mem_cast_compat_Untyped. destruct ot; naive_solver. Qed. *)

  Lemma bytewise_weaken l β P1 P2 ly:
    (∀ b, P1 b → P2 b) →
    l ◁ₗ{β} bytewise P1 ly -∗ l ◁ₗ{β} bytewise P2 ly.
  Proof.
    iIntros (?). iDestruct 1 as (?? HP) "H". iExists _; iFrame.
    iPureIntro; split_and! => //. edestruct HP as (? & ? & ? & ? & ?%Forall_impl); eauto.
  Qed.

  (* To do this, ly should be something more flexible than a type, but I don't think VST has that.
  Lemma split_bytewise n l β P ly:
    (n ≤ sizeof ly)%nat →
    l ◁ₗ{β} bytewise P ly -∗
      l ◁ₗ{β} bytewise P (ly_set_size ly n) ∗
      (l +ₗ n) ◁ₗ{β} bytewise P (ly_offset ly n).
  Proof.
    iIntros (?). iDestruct 1 as (v Hv Hl HP) "Hl".
    rewrite -[v](take_drop n) heap_mapsto_own_state_app.
    iDestruct "Hl" as "[Hl1 Hl2]". iSplitL "Hl1".
    - iExists _. iFrame.
      eapply Forall_take in HP. rewrite /has_layout_val in Hv.
      by rewrite /has_layout_val take_length min_l // Hv.
    - rewrite take_length_le ?Hv //. iExists _. iFrame.
      eapply Forall_drop in HP. eapply has_layout_ly_offset in Hl.
      by rewrite /has_layout_val drop_length Hv.
  Qed.

  Lemma merge_bytewise l β P ly1 ly2:
    (ly1.(ly_size) ≤ ly2.(ly_size))%nat →
    (ly_align ly2 ≤ ly_align ly1)%nat →
    l ◁ₗ{β} bytewise P ly1 -∗
    (l +ₗ ly1.(ly_size)) ◁ₗ{β} (bytewise P (ly_offset ly2 ly1.(ly_size))) -∗
      l ◁ₗ{β} bytewise P ly2.
  Proof.
    iIntros (??).
    iDestruct 1 as (v1 Hv1 Hl1 HP1) "Hl1".
    iDestruct 1 as (v2 Hv2 Hl2 HP2) "Hl2".
    iExists (v1 ++ v2).
    rewrite heap_mapsto_own_state_app Hv1 /has_layout_val app_length Hv1 Hv2.
    iFrame. iPureIntro. split_and!.
    - rewrite {2}/ly_size/=. lia.
    - by apply: has_layout_loc_trans'.
    - by apply Forall_app.
  Qed.

  Lemma bytewise_loc_in_bounds l β P ly:
    l ◁ₗ{β} bytewise P ly -∗ loc_in_bounds l (ly_size ly).
  Proof.
    iDestruct 1 as (v <-) "(_&_&?)".
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.

  Global Instance loc_in_bounds_bytewise β P ly:
    LocInBounds (bytewise P ly) β (ly_size ly).
  Proof. constructor. iIntros (?). by iApply bytewise_loc_in_bounds. Qed. *)

  Lemma subsume_bytewise_ex A l β P1 P2 ly1 ly2 T:
    subsume (l ◁ₗ{β} bytewise P1 ly1) (λ x : A, l ◁ₗ{β} bytewise P2 (ly2 x)) T
      where `{!∀ x, ContainsEx (ly2 x)} :-
              exhale <affine> ⌜∀ b, P1 b → P2 b⌝; ∃ x, exhale <affine> ⌜ly1 = ly2 x⌝; return T x.
  Proof.
    liFromSyntax. iIntros (_) "[% [% [-> HT]]] Hl".
    iExists _. iFrame "HT". by iApply bytewise_weaken.
  Qed.
  Definition subsume_bytewise_ex_inst := [instance subsume_bytewise_ex].
  Global Existing Instance subsume_bytewise_ex_inst | 50.

(*   Lemma subsume_bytewise_eq A l β P1 P2 ly1 ly2
        `{!CanSolve (sizeof ly1 = sizeof ly2)} T:
    <affine> ⌜∀ b, P1 b → P2 b⌝ ∗
    (<affine> ⌜field_compatible ly1 [] (addr_to_val l)⌝ -∗ <affine> ⌜field_compatible ly2 [] l⌝ ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} bytewise P1 ly1) (λ x : A, l ◁ₗ{β} bytewise P2 ly2) T.
  Proof.
    revert select (CanSolve _) => Hsz. unfold CanSolve in *.
    iDestruct 1 as (HPs) "HT". iDestruct 1 as (?? (? & ? & ? & ? & HP)) "?".
    apply (Forall_impl _ _ _ HP) in HPs.
    iDestruct ("HT" with "[//]") as (??) "?". iFrame. rewrite /ty_own /=. eauto.
  Qed.
  Definition subsume_bytewise_eq_inst := [instance subsume_bytewise_eq].
  Global Existing Instance subsume_bytewise_eq_inst | 5.

  Lemma subsume_bytewise_merge A l β P1 P2 ly1 ly2
        `{!CanSolve (ly1.(ly_size) ≤ ly2.(ly_size))%nat} T:
    ⌜∀ b, P1 b → P2 b⌝ ∗
    ⌜ly_align ly2 ≤ ly_align ly1⌝%nat ∗
    ((l +ₗ ly1.(ly_size)) ◁ₗ{β} bytewise P2 (ly_offset ly2 ly1.(ly_size)) ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} bytewise P1 ly1) (λ x : A, l ◁ₗ{β} bytewise P2 ly2) T.
  Proof.
    unfold CanSolve in *.
    iIntros "(%&%&?&%&?) Hl".
    iDestruct (bytewise_weaken with "Hl") as "Hl" => //.
    iExists _. iFrame. iApply (merge_bytewise with "Hl") => //.
  Qed.
  Definition subsume_bytewise_merge_inst := [instance subsume_bytewise_merge].
  Global Existing Instance subsume_bytewise_merge_inst | 10.

  Lemma subsume_bytewise_split A l β P1 P2 ly1 ly2
        `{!CanSolve (ly2.(ly_size) ≤ ly1.(ly_size))%nat} T:
    ⌜∀ b, P1 b → P2 b⌝ ∗
    ⌜ly_align ly2 ≤ ly_align ly1⌝%nat ∗
    ((l +ₗ ly2.(ly_size)) ◁ₗ{β} bytewise P1 (ly_offset ly1 ly2.(ly_size)) -∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} bytewise P1 ly1) (λ x : A, l ◁ₗ{β} bytewise P2 ly2) T.
  Proof.
    unfold CanSolve in *.
    iIntros "(%&%&HT) Hl".
    iDestruct (split_bytewise with "Hl") as "[Hl1 Hl2]" => //.
    iDestruct (bytewise_weaken with "Hl1") as "Hl1" => //.
    iDestruct ("HT" with "Hl2") as (?) "?". iExists _. iFrame.
    iDestruct "Hl1" as (????) "Hl1".
    iExists _; iFrame. iPureIntro; split_and! => //.
    by apply: has_layout_loc_trans'.
  Qed.
  Definition subsume_bytewise_split_inst := [instance subsume_bytewise_split].
  Global Existing Instance subsume_bytewise_split_inst | 10. *)

(* We could do this with the higher-level field offsets instead of direct pointer math.
  Lemma type_add_bytewise v2 β P ly (p : loc) n it T:
    (<affine> ⌜n ∈ it⌝ -∗
      <affine> ⌜0 ≤ n⌝ ∗
      <affine> ⌜n ≤ sizeof ly⌝ ∗
      (p ◁ₗ{β} bytewise P (ly_set_size ly (Z.to_nat n)) -∗ v2 ◁ᵥ n @ int it -∗
       T (val_of_loc (p +ₗ n)) ((p +ₗ n) @ &frac{β} (bytewise P (ly_offset ly (Z.to_nat n))))))
    ⊢ typed_bin_op v2 (v2 ◁ᵥ n @ int it) p (p ◁ₗ{β} bytewise P ly) (PtrOffsetOp u8) (IntOp it) PtrOp T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hint) "Hp". iIntros (Φ) "HΦ".
    move: (Hint) => /val_to_Z_in_range?.
    iDestruct ("HT" with "[//]") as (??) "HT".
    iDestruct (split_bytewise (Z.to_nat n) with "Hp") as "[H1 H2]"; [lia..|].
    rewrite -!(offset_loc_sz1 u8)// Z2Nat.id; [|lia].
    iDestruct (loc_in_bounds_in_bounds with "H2") as "#?".
    iApply wp_ptr_offset; [ by apply val_to_of_loc | done | |].
    { iApply loc_in_bounds_shorten; [|done]; lia. }
    iModIntro. iApply ("HΦ" with "[H2]"). 2: iApply ("HT" with "H1 []").
    - unfold frac_ptr; simpl_type. by iFrame.
    - by iPureIntro.
  Qed.
  Definition type_add_bytewise_inst := [instance type_add_bytewise].
  Global Existing Instance type_add_bytewise_inst. *)
End bytewise.

Notation "bytewise< P , ly >" := (bytewise P ly)
  (only printing, format "'bytewise<' P ',' ly '>'") : printing_sugar.

Global Typeclasses Opaque bytewise.

Notation uninit := (bytewise (λ _, True%type)).

Section uninit.
  Context `{!typeG Σ} {cs : compspecs}.

(*   Context `{!externalGS OK_ty Σ}.
  #[export] Instance VSTGS0 : VSTGS OK_ty Σ := Build_VSTGS _ _ _ _.

  Lemma uninit_own_spec l ly:
    (l ◁ₗ uninit ly)%I ≡ (data_at_ Tsh ly l)%I.
  Proof.
    rewrite /ty_own/=; iSplit.
    - iDestruct 1 as (?? _) "Hl". rewrite /heap_mapsto_own_state. admit.
    - iDestruct 1 as (?) "Hl". iExists v; iFrame. by rewrite Forall_forall.
  Qed. *)

(*   (* This only works for [Own] since [ty] might have interior mutability. *)
  Lemma uninit_mono A l ty ly `{!TCDone (ty.(ty_has_op_type) ly MCNone)} T:
    (∀ v, v ◁ᵥ ty -∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ ty) (λ x : A, l ◁ₗ uninit ly) T.
  Proof.
    unfold TCDone in *; subst. iIntros "HT Hl".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
(*     iDestruct (ty_size_eq with "Hv") as %?; [done|]. *)
    iDestruct ("HT" with "Hv") as (?) "?". iExists _. iFrame.
    iExists v. iFrame. iSplit; first done. 
  Qed.
  (* This rule is handled with a definition and an [Hint Extern] (not
  with an instance) since this rule should only apply ty is not uninit
  as this case is covered by the rules for bytes and the CanSolve can
  be quite expensive. *)
  Definition uninit_mono_inst := [instance uninit_mono].
 *)
(*   (* Typing rule for [Return] (used in [theories/typing/automation.v]). *)
  Lemma type_return Q e fn ls R:
    typed_val_expr e (λ v ty,
      foldr (λ (e : (loc * layout)) T, e.1 ◁ₗ uninit e.2 ∗ T)
      (R v ty)
      (zip ls (fn.(f_args) ++ fn.(f_local_vars)).*2))
    ⊢ typed_stmt (Return e) fn ls R Q.
  Proof.
    iIntros "He" (Hls). wps_bind. iApply "He".
    iIntros (v ty) "Hv HR". iApply wps_return.
    rewrite /typed_stmt_post_cond. move: Hls. move: (f_args fn ++ f_local_vars fn) => lys {fn} Hlys.
    iInduction ls as [|l ls] "IH" forall (lys Hlys); destruct lys as [|ly lys]=> //; csimpl in *; simplify_eq.
    { iExists _. iFrame. }
    iDestruct "HR" as "[Hl HR]".
    iDestruct ("IH" with "[//] Hv HR") as (ty') "[?[??]]".
    iExists _. iFrame.
    rewrite /ty_own/=. iDestruct "Hl" as (????) "Hl".
    iExists _. by iFrame.
  Qed.

  Lemma type_read_move_copy E l ty ot mc a `{!TCDone (ty.(ty_has_op_type) ot MCCopy)} T:
    (∀ v, T v (uninit (ot_layout ot)) ty)
    ⊢ typed_read_end a E l Own ty ot mc T.
  Proof.
    unfold TCDone in *. rewrite /typed_read_end. iIntros "HT Hl".
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hclose".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iExists _, _, _. iFrame. do 2 iSplit => //=.
    iIntros "!# %st Hl Hv". iMod "Hclose". iModIntro.
    iExists _, ty. iSplitL "Hv". { destruct mc => //. by iApply ty_memcast_compat_copy. }
    iSplitR "HT"; [|done]. iExists _. iFrame. iPureIntro. split_and! => //. by apply: Forall_true.
  Qed.
  Definition type_read_move_copy_inst := [instance type_read_move_copy].
  Global Existing Instance type_read_move_copy_inst | 70. *)
End uninit.

Notation "uninit< ly >" := (uninit ly) (only printing, format "'uninit<' ly '>'") : printing_sugar.

(* (* See the definition of [uninit_mono_inst].
   This hint should only apply ty is not uninit as this case is covered by the rules for bytes. *)
Global Hint Extern 5 (Subsume (_ ◁ₗ ?ty) (λ _, _ ◁ₗ (uninit _))%I) =>
  lazymatch ty with
  | uninit _ => fail
  | _ => unshelve notypeclasses refine (uninit_mono_inst _ _ _ _ _)
  end
  : typeclass_instances. *)

Section void.
  Context `{!typeG Σ} {cs : compspecs}.

  Definition void : type := uninit Tvoid.

(*   Lemma type_void T:
    T void ⊢ typed_value Vundef T.
  Proof. iIntros "HT". iExists _. iFrame. unfold void, bytewise; simpl_type. Qed.
  Definition type_void_inst := [instance type_void].
  Global Existing Instance type_void_inst. *)
End void.

Notation zeroed := (bytewise (λ b, b = Byte Byte.zero)).

Section zeroed.
  Context `{!typeG Σ} {cs : compspecs}.

(*  Lemma subsume_uninit_zeroed A p ly1 ly2 T:
    ⌜ly_align ly1 = ly_align ly2⌝ ∗ ⌜ly_size ly2 = 0%nat⌝ ∗ (p ◁ₗ uninit ly1 -∗ ∃ x, T x)
    ⊢ subsume (p ◁ₗ uninit ly1)%I (λ x : A, p ◁ₗ zeroed ly2)%I T.
  Proof.
    iDestruct 1 as (H1 H2) "HT". iIntros "Hp".
    iDestruct (ty_aligned _ (UntypedOp _) MCNone with "Hp") as %Hal; [done|].
    iDestruct (loc_in_bounds_in_bounds with "Hp") as "#Hlib".
    iDestruct ("HT" with "Hp") as (?) "?". iExists _. iFrame.
    iExists []. rewrite Forall_nil /has_layout_loc -H1. repeat iSplit => //.
    rewrite /heap_mapsto_own_state heap_mapsto_eq /heap_mapsto_def /=.
    iSplit => //. iApply (loc_in_bounds_shorten with "Hlib"). lia.
  Qed.
  Definition subsume_uninit_zeroed_inst := [instance subsume_uninit_zeroed].
  Global Existing Instance subsume_uninit_zeroed_inst | 3.*)
End zeroed.
Notation "zeroed< ly >" := (zeroed ly)
  (only printing, format "'zeroed<' ly '>'") : printing_sugar.
