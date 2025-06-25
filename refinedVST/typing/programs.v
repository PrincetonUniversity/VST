From compcert.cfrontend Require Import Clight.
From VST.veric Require Import lifting.
From VST.lithium Require Export proof_state.
From lithium Require Import hooks.
From VST.typing Require Export type.
From VST.typing Require Import type_options.
From VST.floyd Require Import globals_lemmas.

Open Scope Z.

(* int infrastructure *)
Global Instance intsize_eq_dec : EqDecision intsize.
Proof. rewrite /RelDecision /Decision. decide equality. Qed.

Definition val_to_Z (v : val) (t : Ctypes.type) : option Z :=
  match v, t with
  | Vint i, Tint _ Signed _ => Some (Int.signed i)
  | Vint i, Tint sz Unsigned _ => Some (Int.unsigned i)
  | Vlong i, Tlong Signed _ => Some (Int64.signed i)
  | Vlong i, Tlong Unsigned _ => Some (Int64.unsigned i)
  | _, _ => None
  end.

Lemma bitsize_max : forall sz, Z.pow 2 (bitsize_intsize sz) ≤ Int.modulus.
Proof.
  destruct sz; simpl; rep_lia.
Qed.

Lemma bitsize_half_max : forall sz, Z.pow 2 (bitsize_intsize sz - 1) ≤ Int.half_modulus.
Proof.
  destruct sz; simpl; rep_lia.
Qed.

Definition i2v n t :=
  match t with
  | Tint _ _ _ => Vint (Int.repr n)
  | Tlong _ _ => Vlong (Int64.repr n)
  | _ => Vundef
  end.

Definition in_range (n:Z) (t: Ctypes.type) : Prop :=
  match t with
  | Tint IBool _ _ => 0 <= n < 2
  | Tint sz Signed _ => - Z.pow 2 (bitsize_intsize sz - 1) <= n < Z.pow 2 (bitsize_intsize sz - 1)
  | Tint sz Unsigned _ => 0 <= n < Z.pow 2 (bitsize_intsize sz)
  | Tlong Signed _ => Int64.min_signed <= n <= Int64.max_signed
  | Tlong Unsigned _ => 0 <= n <= Int64.max_unsigned
  | _ => False
  end.

Lemma in_range_i2v : forall n t, in_range n t -> tc_val t (i2v n t).
Proof.
  intros; destruct t; try done; simpl in *.
  destruct i; simpl in *; try done.
  - destruct s.
    + rewrite Int.signed_repr; rep_lia.
    + rewrite Int.unsigned_repr; rep_lia.
  - destruct s.
    + rewrite two_power_pos_equiv Int.signed_repr; rep_lia.
    + rewrite Int.unsigned_repr; rep_lia.
  - destruct (decide (n = 0)); subst; auto.
    assert (n = 1) as -> by lia; auto.
Qed.

Definition int_eq v1 v2 :=
  match v1, v2 with
  | Vint i1, Vint i2 => Int.eq i1 i2
  | Vlong i1, Vlong i2 => Int64.eq i1 i2
  | _, _ => false
  end.

Global Instance repable_signed_dec i : Decision (repable_signed i).
refine (repable_signed_dec _). Defined.

Global Instance elem_of_type : ElemOf Z Ctypes.type := in_range.
Global Instance elem_of_type_dec (i : Z) (t:Ctypes.type) : Decision (i ∈ t).
Proof.
  unfold elem_of, elem_of_type.
  destruct t; try solve [
    refine (right _ );  unfold not; intros; inv H].
  - destruct i0; (apply _ || destruct s; apply _).
  - destruct s; apply _.
Qed.

(* Global Instance int_elem_of_type : ElemOf Integers.int Ctypes.type :=
  λ i t, Int.intval i ∈ t. *)

Lemma i2v_to_Z : forall n t, in_range n t -> val_to_Z (i2v n t) t = Some n.
Proof.
  intros.
  destruct t; try done; rewrite /val_to_Z /i2v; destruct s; simpl in H. 
  - rewrite Int.signed_repr //.
    pose proof (bitsize_half_max i).
    destruct i; rep_lia.
  - rewrite Int.unsigned_repr //.
    pose proof (bitsize_max i); destruct i; rep_lia.
  - rewrite Int64.signed_repr //.
  - rewrite Int64.unsigned_repr //.
Qed.

Lemma val_to_Z_in_range : forall t v n, val_to_Z v t = Some n -> tc_val t v -> n ∈ t.
Proof.
  destruct v; try done; destruct t; try done; simpl; intros.
  - destruct i0; [destruct s; inv H; hnf; simpl; try rep_lia..|].
    + rewrite two_power_pos_equiv in H0; lia.
    + destruct H0, s; inv H; hnf.
      * by rewrite Int.signed_zero.
      * by rewrite Int.unsigned_zero.
      * by rewrite Int.signed_one.
      * by rewrite Int.unsigned_one.
  - destruct s; inv H; hnf; rep_lia.
Qed.

Lemma signed_inj_64 : forall i1 i2, Int64.signed i1 = Int64.signed i2 -> i1 = i2.
Proof.
  intros ?? H%(f_equal Int64.repr).
  by rewrite !Int64.repr_signed in H.
Qed.

Lemma unsigned_inj_64 : forall i1 i2, Int64.unsigned i1 = Int64.unsigned i2 -> i1 = i2.
Proof.
  intros ?? H%(f_equal Int64.repr).
  by rewrite !Int64.repr_unsigned in H.
Qed.

Lemma val_of_bool_eq : forall b, Val.of_bool b = Vint (Int.repr (bool_to_Z b)).
Proof.
  intros; rewrite /Val.of_bool /bool_to_Z.
  simple_if_tac; auto.
Qed.

Section judgements.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Class Learnable (P : iProp Σ) := {
    learnable_data : iProp Σ;
    learnable_learn : P ⊢ □ learnable_data;
  }.

(*  Class LearnAlignment (β : own_state) (ty : type) (n : option nat) :=
    learnalign_learn l : l ◁ₗ{β} ty ⊢ ⌜if n is Some n' then l `aligned_to` n' else True⌝
  .*)

  (* Variants of Subsume which don't need the continuation. P is an
  additional sidecondition. Not via iProp_to_Prop since there is no
  continuation. *)
  Class SimpleSubsumePlace (ty1 ty2 : type) (P : iProp Σ) : Prop :=
    simple_subsume_place l β: P ⊢ l ◁ₗ{β} ty1 -∗ l ◁ₗ{β} ty2.
  (* TODO: add infrastructure like SimpleSubsumePlaceR to
  SimpleSubsumeVal. Not sure if it would work because of the movable
  instance. *)
  Class SimpleSubsumeVal cty (ty1 ty2 : type) (P : iProp Σ) : Prop :=
    simple_subsume_val v: P ⊢ v ◁ᵥ|cty| ty1 -∗ v ◁ᵥ|cty| ty2.

  (* This is similar to simplify hyp place (Some 0), but targeted at
  Copy and applying all simplifications at once instead of step by
  step. We need this because copying duplicates a type and we want to
  make it as specific as we can before we do the duplication (e.g.
  destruct all existentials in it). *)
  Definition copy_as (l : address) (β : own_state) (ty : type) (T : type → iProp Σ) : iProp Σ :=
    l ◁ₗ{β} ty -∗ ∃ ty', l ◁ₗ{β} ty' ∗ <affine> ⌜Copyable ty'⌝ ∗ T ty'.
  Class CopyAs (l : address) (β : own_state) (ty : type) : Type :=
    copy_as_proof T : iProp_to_Prop (copy_as l β ty T).

  (* A is the annotation from the code *)
  Definition typed_annot_expr (n : nat) {A} (a : A) (v : val) (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
    (P ={⊤}[∅]▷=∗^n |={⊤}=> T).
  Class TypedAnnotExpr (n : nat) {A} (a : A) (v : val) (P : iProp Σ) : Type :=
    typed_annot_expr_proof T : iProp_to_Prop (typed_annot_expr n a v P T).

  Definition typed_annot_stmt {A} (a : A) (l : address) (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
    (P ={⊤}[∅]▷=∗ T).
  Class TypedAnnotStmt {A} (a : A) (l : address) (P : iProp Σ) : Type :=
    typed_annot_stmt_proof T : iProp_to_Prop (typed_annot_stmt a l P T).

  Definition typed_if {B : bi} (ot : Ctypes.type) (v : val) (P : B) (F : B) (T1 T2 : B) : B :=
    (P -∗ (F ∧ match ot with
          | Tint _ _ _ | Tlong _ _ => ∃ z, <affine> ⌜val_to_Z v ot = Some z⌝ ∗ (if bool_decide (z ≠ 0) then T1 else T2)
          | _ => ∃ b, <affine> ⌜bool_val ot v = Some b⌝ ∗ (if b then T1 else T2) end)).
  Class TypedIf {B : bi} (ot : Ctypes.type) (v : val) (P : B) (F : B) : Type :=
    typed_if_proof T1 T2 : iProp_to_Prop (typed_if ot v P F T1 T2).

  (*** statements *)
(*  Definition typed_stmt_post_cond (fn : function) (ls : list address) (R : val → type → iProp Σ) (v : val) : iProp Σ :=
    (∃ ty, v ◁ᵥ ty ∗ ([∗ list] l;v ∈ ls;(fn.(f_args) ++ fn.(f_local_vars)), l ↦|v.2|) ∗ R v ty)%I. *)
  Context (OK_spec : ext_spec OK_ty) (ge : genv).

  (* Possibly we will want break-types, continue-types, etc. For now, using option to distinguish between
     fallthrough (normal) type and return type. *)
  Definition typed_stmt_post_cond (R : option val → type → assert) : ret_assert :=
    {| RA_normal := R None tytrue;
       RA_break := False;
       RA_continue := False;
       RA_return ret := let v := force_val ret in 
                        ∃ cty ty, ⎡(valinject cty v) ◁ᵥ|cty| ty⎤ ∗ R (Some v) ty |}.
  Definition typed_stmt s f (R : option val → type → assert) : assert :=
    wp OK_spec ge ⊤ f s (typed_stmt_post_cond R)%I.
  Global Arguments typed_stmt _ _ _%_I.

  Lemma typed_stmt_mono s f R1 R2 : (∀ v t, R1 v t ⊢ R2 v t) →
    typed_stmt s f R1 ⊢ typed_stmt s f R2.
  Proof.
    intros. rewrite /typed_stmt. apply wp_conseq; intros; simpl; rewrite ?H; auto.
    iIntros "(% & % & ? & ?)"; rewrite H; eauto with iFrame.
  Qed.

(*  Definition typed_block (P : iProp Σ) (b : label) (fn : function) (ls : list address) (R : val → type → iProp Σ) (Q : gmap label stmt) : iProp Σ :=
    (wps_block P b Q (typed_stmt_post_cond fn ls R)).

  Definition typed_switch (v : val) (ty : type) (it : int_type) (m : gmap Z nat) (ss : list stmt) (def : stmt) (fn : function) (ls : list address) (R : val → type → iProp Σ) (Q : gmap label stmt) : iProp Σ :=
    (v ◁ᵥ ty -∗ ∃ z, ⌜val_to_Z v it = Some z⌝ ∗
      match m !! z with
      | Some i => ∃ s, ⌜ss !! i = Some s⌝ ∗ typed_stmt s fn ls R Q
      | None   => typed_stmt def fn ls R Q
      end).
  Class TypedSwitch (v : val) (ty : type) (it : int_type) : Type :=
    typed_switch_proof m ss def fn ls R Q : iProp_to_Prop (typed_switch v ty it m ss def fn ls R Q).*)

(*  Definition typed_assert (ot : Ctypes.type) (v : val) (P : iProp Σ) (s : stmt) (fn : function) (ls : list address) (R : val → type → iProp Σ) (Q : gmap label stmt) : iProp Σ :=
    (P -∗
       match ot with
       | BoolOp   => ∃ b, ⌜val_to_bool v = Some b⌝ ∗ ⌜b = true⌝ ∗ typed_stmt s fn ls R Q
       | IntOp it => ∃ z, ⌜val_to_Z v it = Some z⌝ ∗ ⌜z ≠ 0⌝ ∗ typed_stmt s fn ls R Q
       | PtrOp    => ∃ l, ⌜val_to_loc v = Some l⌝ ∗ ⌜l ≠ NULL_loc⌝ ∗ wp_if_precond l ∗ typed_stmt s fn ls R Q
       | _        => False
       end)%I.
  Class TypedAssert (ot : op_type) (v : val) (P : iProp Σ) : Type :=
    typed_assert_proof s fn ls R Q : iProp_to_Prop (typed_assert ot v P s fn ls R Q).*)

  (*** expressions *)

  (* worked out with Arnaud Daby-Seesaram; not used, but inspiration for wp_expr
  Definition eval_rel (*(t : type)*) (e : expr) (v : val) (rho : environ)
    : iProp Σ :=
    ∀ m, juicy_mem.mem_auth m -∗
           ⌜forall ge ve te,
              cenv_sub cenv_cs (genv_cenv ge) ->
              rho = construct_rho (filter_genv ge) ve te ->
              Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)⌝.*)

  Definition typed_val_expr f (e : expr) (T : val → type → assert) : assert :=
    (∀ Φ, (∀ v (ty : type), ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ T v ty -∗ Φ v) -∗ wp_expr ge ⊤ f e Φ).
  Global Arguments typed_val_expr _ _%_I.

  (* FIXME sounds like typed_addr_of, although typed_addr_of is for typing `&e`; are they the same?  *)
  Definition typed_lvalue f β e T : assert :=
    (∀ Φ:address->assert, 
      (∀ (l:address) (ty : type),
        ⎡l ◁ₗ{β} ty⎤ (* typed_write_end has this so maybe here needs it too? *) 
        -∗ T l β ty -∗ Φ l)
      -∗ wp_lvalue ge ⊤ f e Φ).
  Global Arguments typed_lvalue _ _ _ _%_I.
  Class TypedLvalue f β (e : expr) : Type :=
    typed_lvalue_proof T : iProp_to_Prop (typed_lvalue f β e T).

  Definition typed_value (cty : Ctypes.type) (v : val) (T : type → assert) : assert :=
    (∃ (ty: type), ⎡v ◁ᵥₐₗ|cty| ty⎤ ∗ T ty).
  Class TypedValue (cty : Ctypes.type) (v : val) : Type :=
    typed_value_proof T : iProp_to_Prop (typed_value cty v T).

  (* `op (v1:t) (v2:t)` evaluates to (v:cty) *)
  Definition typed_val_binop op t1 v1 t2 v2 cty (T : val → type → assert) : assert :=
    (∀ Φ, (∀ v (ty : type), ⎡v ◁ᵥₐₗ|cty| ty⎤  -∗ T v ty -∗ Φ v) -∗ wp_binop ge ⊤ op t1 v1 t2 v2 Φ).
  Global Arguments typed_val_binop _ _ _ _ _ _ _%_I.

  Definition typed_bin_op (v1 : val) (P1 : assert) (v2 : val) (P2 : assert) (o : Cop.binary_operation) (t1 t2 t: Ctypes.type) (T : val → type → assert) : assert :=
    (P1 -∗ P2 -∗ typed_val_binop o t1 v1 t2 v2 t T)%I.

  Class TypedBinOp (v1 : val) (P1 : assert) (v2 : val) (P2 : assert) (o : Cop.binary_operation) (ot1 ot2 ot: Ctypes.type) : Type :=
    typed_bin_op_proof T : iProp_to_Prop (typed_bin_op v1 P1 v2 P2 o ot1 ot2 ot T).

  (* `op (v1:t)` evaluates to (v:cty) *)
  Definition typed_val_unop op t cty v1 (T : val → type → assert) : assert :=
    (∀ Φ, (∀ v (ty : type), ⎡v ◁ᵥₐₗ|cty| ty⎤ -∗ T v ty -∗ Φ v) -∗ wp_unop ⊤ op t v1 Φ).
  Global Arguments typed_val_unop _ _ _ _%_I.

  Definition typed_un_op (v : val) (P : assert) (o : Cop.unary_operation) (t cty : Ctypes.type) (T : val → type → assert) : assert :=
    (P -∗ typed_val_unop o t cty v T)%I.

  Class TypedUnOp (v : val) (P : assert) (o : Cop.unary_operation) (t cty : Ctypes.type) : Type :=
    typed_un_op_proof T : iProp_to_Prop (typed_un_op v P o t cty T).

  (* FIXME this probably does not work; maybe providing a list of cty?  *)
  Definition typed_exprs f (el : list expr) (tl : list Ctypes.type) (T : list val → list type → assert) : assert :=
    (∀ Φ, (∀ vl (tys : list type), ([∗ list] v;ty∈vl;tys, ∃ cty, ⎡v ◁ᵥₐₗ|cty| ty⎤) -∗ T vl tys -∗ Φ vl) -∗ wp_exprs ge ⊤ f el tl Φ).
  Global Arguments typed_exprs _ _ _ _%_I.

  (* can we rewrite this to take vals directly after all? We'd have to replace typed_stmt with sufficient
     conditions for a call to be safe. *)
  Definition typed_call (e : expr) (P : assert) (el : list expr) (tys : list type) (T : option val → type → assert) : assert :=
    match typeof e with
    | Tfunction ts _ _ => (∀ f, P -∗ (*(typed_exprs el ts (λ _ tl, <affine> ⌜tl = tys⌝)) -∗*) typed_stmt (Scall None e el) f T)%I
    | _ => False
    end.
  Class TypedCall (e : expr) (P : assert) (el : list expr) (tys : list type) : Type :=
    typed_call_proof T : iProp_to_Prop (typed_call e P el tys T).

(* There does not seem to be a copy stmt in Clight, just Sassign 
  Definition typed_copy_alloc_id (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (ot : op_type) (T : val → type → iProp Σ) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr (CopyAllocId ot v1 v2) T).

  Class TypedCopyAllocId (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (ot : op_type) : Type :=
    typed_copy_alloc_id_proof T : iProp_to_Prop (typed_copy_alloc_id v1 P1 v2 P2 ot T).
*)

(*
  Definition typed_cas (ot : op_type) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (v3 : val) (P3 : iProp Σ)  (T : val → type → iProp Σ) : iProp Σ :=
    (P1 -∗ P2 -∗ P3 -∗ typed_val_expr (CAS ot v1 v2 v3) T).
  Class TypedCas (ot : op_type) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (v3 : val) (P3 : iProp Σ) : Type :=
    typed_cas_proof T : iProp_to_Prop (typed_cas ot v1 P1 v2 P2 v3 P3 T).
*)

  (* This does not allow overloading the macro based on the type of
  es. Is this a problem? There is a work around where the rule inserts
  another judgment that allows type-based overloading. *)
(*  Definition typed_macro_expr (m : list expr → expr) (es : list expr) (T : val → type → iProp Σ) : iProp Σ :=
    (typed_val_expr (m es) T).
  Class TypedMacroExpr (m : list expr → expr) (es : list expr) : Type :=
    typed_macro_expr_proof T : iProp_to_Prop (typed_macro_expr m es T).*)

  (*** places *)
  (** [typed_write atomic e ot v ty] typechecks a write with op_type
  ot of value [v] of type [ty] to the expression [e]. [atomic] says
  whether the write is an atomic write. The typing rule for [typed_write]
  typechecks [e] and then dispatches to [typed_write_end]. *)
 (* Ke: maybe v should be `reptype ot`? *)

  Definition typed_write f (atomic : bool) (e : expr) (ot : Ctypes.type) (v : val) (ty : type) (T : assert) : assert :=
    let E := if atomic then ∅ else ⊤ in
    (∀ (Φ: address->assert),
        (∀ (l:address), (⎡v ◁ᵥₐₗ|ot| ty⎤ ={⊤, E}=∗
                <affine> ⌜(valinject ot v) `has_layout_val` ot⌝ ∗
                 ⎡ l ↦_|ot| ⎤ ∗
                (* Ke : maybe we need later afterall because write is only done a write statement after? *)
                ▷(⎡ l ↦|ot| (valinject ot v) ⎤ ={E, ⊤}=∗ T))
              -∗ Φ l) -∗
       wp_lvalue ge ⊤ f e Φ)%I.

  (** [typed_read atomic e ot memcast] typechecks a read with op_type
  ot of the expression [e]. [atomic] says whether the read is an
  atomic read and [memcast] says whether a memcast is performed during
  the read. The typing rule for [typed_read] typechecks [e] and then
  dispatches to [typed_read_end] *)
  (* FIXME cast need whole memory? *)
Definition typed_read f (atomic : bool) (e : expr) (ot : Ctypes.type) (memcast : bool) (m: mem) (T : val → type → assert) : assert :=
    let E := if atomic then ∅ else ⊤ in
    (∀ (Φ: val->assert),
       (∀ (l:address), 
          (|={⊤, E}=> ∃ v q (ty : type), ⌜l `has_layout_loc` ot⌝ ∗ ⌜(valinject ot v) `has_layout_val` ot⌝ ∗
                        ⎡ l ↦{q}|ot| (valinject ot v) ⎤ ∗ ▷ ⎡(valinject ot v) ◁ᵥ|ot| ty⎤ ∗ 
                        ▷ (∀ st, ⎡ l ↦{q}|ot| (valinject ot v) ⎤ -∗ ⎡(valinject ot v) ◁ᵥ|ot| ty⎤ ={E, ⊤}=∗ 
                        ∃ (ty' : type) v', 
                          ⌜Some v'=if memcast then Cop.sem_cast v ot st m else Some v⌝ ∧
                          ⎡(valinject (if memcast then st else ot) v') ◁ᵥ|(if memcast then st else ot)| ty'⎤ ∗
                          T v' ty')) 
        -∗ Φ l) -∗
     wp_expr ge ⊤ f e Φ)%I.

  (** [typed_addr_of e] typechecks an address of operation on the expression [e].
  The typing rule for [typed_addr_of] typechecks [e] and then dispatches to [typed_addr_of_end]*)
  Definition typed_addr_of f (e : expr) (T : address → own_state → type → assert) : assert :=
    ∀ (Φ: val->assert),
       (∀ (l : address) β ty, ⎡l ◁ₗ{β} ty⎤ -∗ T l β ty -∗ Φ l) -∗
       wp_expr ge ⊤ f e Φ.

  (** [typed_read_end atomic E l β ty ot memcast] typechecks a read with op_type
  ot of the location [l] with type [l ◁ₗ{β} ty]. [atomic] says whether the read is an
  atomic read, [E] gives the current mask, and [memcast] says whether a memcast is
  performed during the read. *)
  Definition typed_read_end (atomic : bool) (E : coPset) (l : address) (β : own_state) (ty : type) (ot : Ctypes.type) (memcast : bool) (m:mem) (T : val → type → type → assert) : assert :=
    (let E' := if atomic then ∅ else E in
    ⎡l◁ₗ{β}ty⎤ ={E, E'}=∗ ∃ q v (ty2 : type),
    ⌜l `has_layout_loc` ot⌝ ∗ ⌜(valinject ot v) `has_layout_val` ot⌝ ∗
    ⎡l↦{q}|ot| valinject ot v⎤ ∗ ▷ ⎡(valinject ot v) ◁ᵥ|ot| ty2⎤ ∗
         ▷ (∀ st, ⎡l↦{q}|ot| (valinject ot v)⎤ -∗ ⎡(valinject ot v) ◁ᵥ|ot| ty2⎤ ={E', E}=∗
            ∃ ty' (ty3 : type) (v':val), ⌜Some v'=if memcast then Cop.sem_cast v ot st m else Some v⌝ ∧
              ⎡(valinject (if memcast then st else ot) v') ◁ᵥ|(if memcast then st else ot)| ty3⎤ ∗
              ⎡l◁ₗ{β} ty'⎤ ∗ T v' ty' ty3))%I.

  Class TypedReadEnd (atomic : bool) (E : coPset) (l : address) (β : own_state) (ty : type) (ot : Ctypes.type) (m:mem) (memcast : bool) : Type :=
    typed_read_end_proof T : iProp_to_Prop (typed_read_end atomic E l β ty ot memcast m T).

  (** [typed_write atomic E ot v1 ty1 l2 β2 ty2] typechecks a write with op_type
  ot of value [v1] of type [ty1] to the location [l2] with type [l2 ◁ₗ{β2} ty].
  [atomic] says whether the write is an atomic write and [E] gives the current mask. *)
  Definition typed_write_end (atomic : bool) (E : coPset) (ot : Ctypes.type) (v1 : val) (ty1 : type) (l2 : address) (β2 : own_state) (ty2 : type) (T : type → assert) : assert :=
    let E' := if atomic then ∅ else E in
    (⎡l2 ◁ₗ{β2} ty2⎤ -∗ 
    (⎡v1 ◁ᵥₐₗ|ot| ty1⎤ ={E, E'}=∗
       <affine> ⌜(valinject ot v1) `has_layout_val` ot⌝ ∗
      ⎡ l2↦_|ot| ⎤ ∗ 
      ▷ (⎡ l2 ↦|ot| (valinject ot v1) ⎤ ={E', E}=∗ ∃ ty3, ⎡l2 ◁ₗ{β2} ty3⎤ ∗ T ty3)))%I.
  Class TypedWriteEnd (atomic : bool) (E : coPset) (ot : Ctypes.type) (v1 : val) (ty1 : type) (l2 : address) (β2 : own_state) (ty2 : type) : Type :=
    typed_write_end_proof T : iProp_to_Prop (typed_write_end atomic E ot v1 ty1 l2 β2 ty2 T).

  (** [typed_addr_of_end l β ty] typechecks an address of operation on the location [l]
  with type [l ◁ₗ{β} ty]. *)
  Definition typed_addr_of_end (l : address) (β : own_state) (ty : type) (T : own_state → type → type → assert) : assert :=
    (⎡l◁ₗ{β}ty⎤ ={⊤}=∗ ∃ β2 ty2 ty', ⎡l◁ₗ{β2}ty2⎤ ∗ ⎡l◁ₗ{β}ty'⎤ ∗ T β2 ty2 ty')%I.
  Class TypedAddrOfEnd (l : address) (β : own_state) (ty : type) : Type :=
    typed_addr_of_end_proof T : iProp_to_Prop (typed_addr_of_end l β ty T).

  (*** typed places *)
  (* This defines what place expressions can contain. We cannot reuse
  W.ectx_item because of BinOpPCtx since there the root of the place
  expression is not in evaluation position. *)
  (* TODO: Should we track location information here? *)
(*  Inductive place_ectx_item :=
  | DerefPCtx (o : order) (ot : op_type) (memcast : bool)
  | GetMemberPCtx (s : struct_layout) (m : var_name)
  | GetMemberUnionPCtx (ul : union_layout) (m : var_name)
  | AnnotExprPCtx (n : nat) {A} (x : A)
    (* for PtrOffsetOp, second ot must be PtrOp *)
  | BinOpPCtx (op : bin_op) (ot : op_type) (v : val) (ty : type)
    (* for ptr-to-ptr casts, ot must be PtrOp *)
  | UnOpPCtx (op : un_op)
  .

  (* Computes the WP one has to prove for the place ectx_item Ki
  applied to the location l. *)
  Definition place_item_to_wp (Ki : place_ectx_item) (Φ : loc → iProp Σ) (l : loc) : iProp Σ :=
    match Ki with
    | DerefPCtx o ot mc => WP !{ot, o, mc} l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberPCtx sl m => WP l at{sl} m {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberUnionPCtx ul m => WP l at_union{ul} m {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | AnnotExprPCtx n x => WP AnnotExpr n x l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    (* we have proved typed_val_expr e1 before so we can use v ◁ᵥ ty here *)
    | BinOpPCtx op ot v ty => v ◁ᵥ ty -∗ WP BinOp op ot PtrOp v l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | UnOpPCtx op => WP UnOp op PtrOp l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    end%I.
  Definition place_to_wp (K : list place_ectx_item) (Φ : loc → iProp Σ) : (loc → iProp Σ) := foldr place_item_to_wp Φ K.
  Lemma place_to_wp_app (K1 K2 : list place_ectx_item) Φ : place_to_wp (K1 ++ K2) Φ = place_to_wp K1 (place_to_wp K2 Φ).
  Proof. apply foldr_app. Qed.

  Lemma place_item_to_wp_mono K Φ1 Φ2 l:
    place_item_to_wp K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_item_to_wp K Φ2 l.
  Proof.
    iIntros "HP HΦ". move: K => [o ot mc|sl m|ul m|n A x|op ot v ty|op]//=.
    5: iIntros "Hv".
    1-4,6: iApply (@wp_wand with "HP").
    6: iApply (@wp_wand with "[Hv HP]"); first by iApply "HP".
    all: iIntros (?); iDestruct 1 as (l' ->) "HΦ1".
    all: iExists _; iSplit => //; by iApply "HΦ".
  Qed.

  Lemma place_to_wp_mono K Φ1 Φ2 l:
    place_to_wp K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_to_wp K Φ2 l.
  Proof.
    iIntros "HP HΦ".
    iInduction (K) as [] "IH" forall (l) => /=. 1: by iApply "HΦ".
    iApply (place_item_to_wp_mono with "HP").
    iIntros (l') "HP". by iApply ("IH" with "HP HΦ").
  Qed.

  Fixpoint find_place_ctx (e : W.expr) : option ((list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    match e with
    | W.Loc l => Some (λ T, T [] l)
    | W.Deref o ot mc e => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [DerefPCtx o ot mc]) l))
    | W.GetMember e sl m => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [GetMemberPCtx sl m]) l))
    | W.GetMemberUnion e ul m => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [GetMemberUnionPCtx ul m]) l))
    | W.AnnotExpr n x e => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [AnnotExprPCtx n x]) l))
    | W.LocInfoE a e => find_place_ctx e
    (* Here we use the power of having a continuation available to add
    a typed_val_expr. It is important that this happens before we get
    to place_to_wp_mono since we will need to give up ownership of the
    root of the place expression once we hit it. This allows us to
    support e.g. a[a[0]]. *)
    | W.BinOp op ot PtrOp e1 e2 => T' ← find_place_ctx e2; Some (λ T, typed_val_expr (W.to_expr e1) (λ v ty, T' (λ K l, T (K ++ [BinOpPCtx op ot v ty]) l)))
    | W.UnOp op PtrOp e => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [UnOpPCtx op]) l))
    (* TODO: Is the existential quantifier here a good idea or should this be a fullblown judgment? *)
    | W.UnOp op (IntOp it) e => Some (λ T, typed_val_expr (UnOp op (IntOp it) (W.to_expr e)) (λ v ty, v ◁ᵥ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T [] l)%I)
    | W.LValue e => Some (λ T, typed_val_expr (W.to_expr e) (λ v ty, v ◁ᵥ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T [] l)%I)
    | _ => None
    end.

  Class IntoPlaceCtx (e : expr) (T : (list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    into_place_ctx Φ Φ': (⊢ T Φ' -∗ (∀ K l, Φ' K l -∗ place_to_wp K (Φ ∘ val_of_loc) l) -∗ WP e {{ Φ }}).

  Section find_place_ctx_correct.
  Arguments W.to_expr : simpl nomatch.
  Lemma find_place_ctx_correct e T:
    find_place_ctx e = Some T →
    IntoPlaceCtx (W.to_expr e) T.
  Proof.
    elim: e T => //= *.
    all: iIntros (Φ Φ') "HT HΦ'".
    2,3: case_match.
    all: try match goal with
    |  H : ?x ≫= _ = Some _ |- _ => destruct x as [?|] eqn:Hsome
    end; simplify_eq/=.
    all: try match goal with
    |  H : context [IntoPlaceCtx _ _] |- _ => rename H into IH
    end.
    1: iApply @wp_value; by iApply ("HΦ'" with "HT").
    1: {
      iApply "HT". iIntros (v ty) "Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
        by iApply ("HΦ'" $! []).
    }
    4: {
      rewrite /LValue. iApply "HT". iIntros (v ty) "Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
      by iApply ("HΦ'" $! []).
    }
    2: wp_bind; rewrite -!/(W.to_expr _).
    2: iApply "HT"; iIntros (v ty) "Hv HT".
    2: iDestruct (IH with "HT") as "HT" => //.
    1, 3-6: iDestruct (IH with "HT") as " HT" => //.
    all: wp_bind; iApply "HT".
    all: iIntros (K l) "HT" => /=.
    all: iDestruct ("HΦ'" with "HT") as "HΦ"; rewrite place_to_wp_app /=.
    all: iApply (place_to_wp_mono with "HΦ"); iIntros (l') "HWP" => /=.
    6: iApply (@wp_wand with "[Hv HWP]"); first by iApply "HWP".
    1-5: iApply (@wp_wand with "HWP").
    all: iIntros (?); by iDestruct 1 as (? ->) "$".
  Qed.
  End find_place_ctx_correct.
*)

  (* TODO: have something like typed_place_cond which uses a fraction? Seems *)
  (* tricky since stating that they have the same size requires that ty1 *)
  (* and ty2 are movable (which they might not be) *)
  (* Ke: ignoring typed_place_context for now, might need it later *)
  (* Definition typed_place (l1 : address) (β1 : own_state) (ty1 : type) (T : address → own_state → type → (type → type) → (type → assert) → assert) : assert :=
    (∀ Φ, ⎡l1 ◁ₗ{β1} ty1⎤ -∗
       (∀ (l2 : address) β2 ty2 typ R, ⎡l2 ◁ₗ{β2} ty2⎤ -∗ (∀ ty', ⎡l2 ◁ₗ{β2} ty'⎤ ={⊤}=∗ ⎡l1 ◁ₗ{β1} typ ty'⎤ ∗ R ty') -∗ T l2 β2 ty2 typ R -∗ Φ l2) -∗ (wp_expr (EConst l) Φ))%I.
  Class TypedPlace  (l1 : address) (β1 : own_state) (ty1 : type) : Type :=
    typed_place_proof T : iProp_to_Prop (typed_place l1 β1 ty1 T). *)

End judgements.

(*Ltac solve_into_place_ctx :=
  match goal with
  | |- IntoPlaceCtx ?e ?T =>
      let e' := W.of_expr e in
      change_no_check (IntoPlaceCtx (W.to_expr e') T);
      refine (find_place_ctx_correct _ _ _); rewrite/=/W.to_expr/=; done
  end.
Global Hint Extern 0 (IntoPlaceCtx _ _) => solve_into_place_ctx : typeclass_instances.*)

Global Hint Mode Learnable + + : typeclass_instances.
(*Global Hint Mode LearnAlignment + + + + - : typeclass_instances.*)
Global Hint Mode CopyAs + + + + + + + : typeclass_instances.
Global Hint Mode SimpleSubsumePlace + + + + + ! - : typeclass_instances.
Global Hint Mode SimpleSubsumeVal + + + + + ! ! - : typeclass_instances.
Global Hint Mode TypedIf + + + + + : typeclass_instances.
(* Global Hint Mode TypedAssert + + + + + + : typeclass_instances. *)
Global Hint Mode TypedValue + + + + + + : typeclass_instances.
Global Hint Mode TypedBinOp + + + + + + + + + + + + + : typeclass_instances.
Global Hint Mode TypedUnOp + + + + + + + + + : typeclass_instances.
Global Hint Mode TypedCall + + + + + + + + + + : typeclass_instances.
(*Global Hint Mode TypedCopyAllocId + + + + + + + : typeclass_instances. *)
Global Hint Mode TypedReadEnd + + + + + + + + + + + + : typeclass_instances.
Global Hint Mode TypedWriteEnd + + + + + + + + + + + + : typeclass_instances.
Global Hint Mode TypedAddrOfEnd + + + + + + + : typeclass_instances.
(* Global Hint Mode TypedPlace + + + + + + : typeclass_instances. *)
Global Hint Mode TypedAnnotExpr + + + + + + + + : typeclass_instances.
Global Hint Mode TypedAnnotStmt + + + + + + + : typeclass_instances.
(* Global Hint Mode TypedMacroExpr + + + + : typeclass_instances. *)
Arguments typed_annot_expr : simpl never.
Arguments typed_annot_stmt : simpl never.
(* Arguments typed_macro_expr : simpl never. *)
Arguments learnable_data {_ _} _.
(*Arguments learnalign_learn {_ _ _ _ _} _.*)

Section proper.
  Context `{!typeG OK_ty Σ} {cs : compspecs} (ge: genv).

  Lemma simplify_hyp_place_eq ty1 ty2 (Heq : ty1 ≡@{type} ty2) l β T:
    (l ◁ₗ{β} ty2 -∗ T) ⊢ simplify_hyp (l◁ₗ{β} ty1) T.
  Proof. iIntros "HT ?". rewrite Heq. by iApply "HT". Qed.

  Lemma simplify_goal_place_eq ty1 ty2 (Heq : ty1 ≡@{type} ty2) l β T:
    l ◁ₗ{β} ty2 ∗ T ⊢ simplify_goal (l◁ₗ{β} ty1) T.
  Proof. rewrite Heq. iIntros "$". Qed.

  Lemma simplify_hyp_val_eq cty ty1 ty2 (Heq : ty1 ≡@{type} ty2) v T:
    (v ◁ᵥ|cty| ty2 -∗ T) ⊢ simplify_hyp (v ◁ᵥ|cty| ty1) T.
  Proof. iIntros "HT ?". rewrite Heq. by iApply "HT". Qed.

  Lemma simplify_goal_val_eq cty ty1 ty2 (Heq : ty1 ≡@{type} ty2) v T:
    v ◁ᵥ|cty| ty2 ∗ T ⊢ simplify_goal (v ◁ᵥ|cty| ty1) T.
  Proof. rewrite Heq. iIntros "$". Qed.

(*  Lemma typed_place_subsume' P l ty1 β T :
    (l ◁ₗ{β} ty1 -∗ ∃ ty2, l ◁ₗ{β} ty2 ∗ typed_place P l β ty2 T) ⊢ typed_place P l β ty1 T.
  Proof.
    iIntros "Hsub" (Φ) "Hl HΦ". iDestruct ("Hsub" with "Hl") as (ty2) "[Hl HP]". by iApply ("HP" with "Hl").
  Qed.

  Lemma typed_place_subsume P l ty1 ty2 β T :
    subsume (l ◁ₗ{β} ty1) (λ _ : unit, l ◁ₗ{β} ty2) (λ _, typed_place P l β ty2 T) ⊢ typed_place P l β ty1 T.
  Proof.
    iIntros "Hsub". iApply typed_place_subsume'.
    iIntros "Hl". iExists _. iDestruct ("Hsub" with "Hl") as (_) "$".
  Qed.*)

  (** wand lemmas *)
  Lemma typed_val_expr_wand f e T1 T2:
    typed_val_expr ge f e T1 -∗
    (∀ v ty, T1 v ty -∗ T2 v ty) -∗
    typed_val_expr ge f e T2.
  Proof.
    iIntros "He HT" (Φ) "HΦ".
    iApply "He". iIntros (v ty) "Hv Hty".
    iApply ("HΦ" with "Hv"). by iApply "HT".
  Qed.

  Lemma typed_if_wand ot v (P F : iProp Σ) T1 T2 T1' T2':
    typed_if ot v P F T1 T2 -∗
    <affine> ((T1 -∗ T1') ∧ (T2 -∗ T2')) -∗
    typed_if ot v P F T1' T2'.
  Proof.
    iIntros "Hif HT Hv". iDestruct ("Hif" with "Hv") as "Hif".
    iSplit; [iDestruct "Hif" as "[$ _]" | iDestruct "Hif" as "[_ Hif]"].
    rewrite bi.affinely_elim.
    destruct ot; iDestruct "Hif" as (b ?) "HC"; iExists b; (iSplit; first done); (simple_if_tac;
      (iDestruct "HT" as "[_ HT]"; by iApply "HT") || (iDestruct "HT" as "[HT _]"; by iApply "HT")).
  Qed.

  Lemma typed_bin_op_wand v1 P1 Q1 v2 P2 Q2 op ot1 ot2 ot T:
    typed_bin_op ge v1 Q1 v2 Q2 op ot1 ot2 ot T -∗
    (P1 -∗ Q1) -∗
    (P2 -∗ Q2) -∗
    typed_bin_op ge v1 P1 v2 P2 op ot1 ot2 ot T.
  Proof.
    iIntros "H Hw1 Hw2 H1 H2".
    iApply ("H" with "[Hw1 H1]"); [by iApply "Hw1"|by iApply "Hw2"].
  Qed.

  Lemma typed_un_op_wand v P Q op t cty T:
    typed_un_op v Q op t cty T -∗
    (P -∗ Q) -∗
    typed_un_op v P op t cty T.
  Proof.
    iIntros "H Hw HP". iApply "H". by iApply "Hw".
  Qed.

  Lemma type_val_expr_mono_strong f e T :
    typed_val_expr ge f e (λ v ty,
      ∃ ty', subsume ⎡v ◁ᵥₐₗ|typeof e| ty⎤ (λ _ : unit, ⎡v ◁ᵥₐₗ|typeof e| ty'⎤) (λ _, T v ty'))%I
    -∗ typed_val_expr ge f e T.
  Proof.
    iIntros "HT". iIntros (Φ) "HΦ".
    iApply "HT". iIntros (v ty) "Hv HT".
    iDestruct "HT" as (ty') "HT".
    iPoseProof ("HT" with "Hv") as (?) "[Hv HT']".
    iApply ("HΦ" with "Hv HT'").
  Qed.


(*
  (** typed_read_end *)
  Lemma typed_read_end_mono_strong (a : bool) E1 E2 l β ty ot mc T:
    (if a then ∅ else E2) = (if a then ∅ else E1) →
    (l ◁ₗ{β} ty ={E1, E2}=∗ ∃ β' ty' P, l ◁ₗ{β'} ty' ∗ ▷ P ∗
       typed_read_end a E2 l β' ty' ot mc (λ v ty2 ty3,
          P -∗ l ◁ₗ{β'} ty2 -∗ v ◁ᵥ ty3 ={E2, E1}=∗
          ∃ ty2' ty3', l ◁ₗ{β} ty2' ∗ v ◁ᵥ ty3' ∗ T v ty2' ty3')) -∗
    typed_read_end a E1 l β ty ot mc T.
  Proof.
    iIntros (Ha) "HT Hl". iMod ("HT" with "Hl") as (β' ty' P) "(Hl&HP&HT)".
    iMod ("HT" with " Hl") as (?????) "(Hl&Hv&HT)". rewrite Ha.
    iModIntro. iExists _, _, _.
    iFrame "Hl Hv". iSplit; [done|]. iSplit; [done|].
    iIntros "!> %st Hl Hv". iMod ("HT" with "Hl Hv") as (? ty3) "(Hcast&Hl&HT)".
    iMod ("HT" with "HP Hl Hcast") as (ty2' ty3') "(?&?&?)". iExists _, _. by iFrame.
  Qed.

  Lemma typed_read_end_wand (a : bool) E l β ty ot mc T T':
    typed_read_end a E l β ty ot mc T' -∗
    (∀ v ty1 ty2, T' v ty1 ty2 -∗ T v ty1 ty2) -∗
    typed_read_end a E l β ty ot mc T.
  Proof.
    iIntros "HT Hw Hl". iMod ("HT" with "Hl") as (???) "(%&%&Hl&Hv&HT)".
    iModIntro. iExists _, _, _.
    iFrame "Hl Hv". iSplit; [done|]. iSplit; [done|].
    iIntros "!> %st Hl Hv". iMod ("HT" with "Hl Hv") as (? ty3) "(Hcast&Hl&HT)".
    iExists _, _. iFrame. by iApply "Hw".
  Qed.

  Lemma fupd_typed_read_end a E l β ty ot mc T:
    (|={E}=> typed_read_end a E l β ty ot mc T)
    ⊢ typed_read_end a E l β ty ot mc T.
  Proof. iIntros ">H". by iApply "H". Qed.

  (* TODO: can this be Global? *)
  Local Typeclasses Opaque typed_read_end.
  Global Instance elim_modal_fupd_typed_read_end p a E l β ty ot mc T P :
    ElimModal True p false (|={E}=> P) P (typed_read_end a E l β ty ot mc T) (typed_read_end a E l β ty ot mc T).
  Proof.
    iIntros (?) "[HP HT]".
    rewrite bi.intuitionistically_if_elim -{2}fupd_typed_read_end.
    iMod "HP". by iApply "HT".
  Qed.

  Global Instance is_except_0_typed_read_end a E l β ty ot mc T : IsExcept0 (typed_read_end a E l β ty ot mc T).
  Proof. by rewrite /IsExcept0 -{2}fupd_typed_read_end -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_fupd_typed_read_end_atomic p E1 E2 l β ty ot mc T P:
    ElimModal True p false
            (|={E1,E2}=> P) P
            (typed_read_end true  E1 l β ty ot mc T)
            (typed_read_end true E2 l β ty ot mc (λ v ty ty', |={E2,E1}=> T v ty ty'))%I
            | 100.
  Proof.
    iIntros (?) "[HP HT]". rewrite bi.intuitionistically_if_elim.
    iApply typed_read_end_mono_strong; [done|]. iIntros "Hl". iMod "HP". iModIntro.
    iExists _, _, True%I. iFrame. iSplit; [done|].
    iApply (typed_read_end_wand with "(HT HP)").
    iIntros (v ty1 ty2) "HT _ Hl Hv". iMod "HT". iModIntro. iExists _, _. iFrame.
  Qed.

  Global Instance elim_acc_typed_read_end_atomic {X} E1 E2 α β γ l b ty ot mc T :
    ElimAcc (X:=X) True
            (fupd E1 E2) (fupd E2 E1)
            α β γ
            (typed_read_end true E1 l b ty ot mc T)
            (λ x, typed_read_end true E2 l b ty ot mc (λ v ty ty', |={E2}=> β x ∗ (γ x -∗? T v ty ty')))%I | 100.
  Proof.
    iIntros (?) "Hinner Hacc".
    iMod "Hacc" as (x) "[Hα Hclose]".
    iApply (typed_read_end_wand with "(Hinner Hα)").
    iIntros (v ty1 ty2) ">[Hβ HT]". iMod ("Hclose" with "Hβ"). by iApply "HT".
  Qed.

  (** typed_write_end *)
  Lemma typed_write_end_mono_strong (a : bool) E1 E2 ot v1 ty1 l2 β2 ty2 T:
    (if a then ∅ else E2) = (if a then ∅ else E1) →
    (v1 ◁ᵥ ty1 -∗ l2 ◁ₗ{β2} ty2 ={E1, E2}=∗ ∃ ty1' β2' ty2' P,
       v1 ◁ᵥ ty1' ∗ l2 ◁ₗ{β2'} ty2' ∗ ▷ P ∗
       typed_write_end a E2 ot v1 ty1' l2 β2' ty2' (λ ty3,
          P -∗ l2 ◁ₗ{β2'} ty3 ={E2, E1}=∗
          ∃ ty3', l2 ◁ₗ{β2} ty3' ∗ T ty3')) -∗
    typed_write_end a E1 ot v1 ty1 l2 β2 ty2 T.
  Proof.
    iIntros (Ha) "HT Hl Hv". iMod ("HT" with "Hv Hl") as (ty1' β2' ty2' P) "(Hv&Hl&HP&HT)".
    iMod ("HT" with "Hl Hv") as (?) "(?&HT)". rewrite Ha.
    iModIntro. iSplit; [done|]. iFrame. iIntros "!> Hl". iMod ("HT" with "Hl") as (ty3) "(Hl&HT)".
    iMod ("HT" with "HP Hl") as (ty3') "(?&?)". iExists  _. by iFrame.
  Qed.

  Lemma typed_write_end_wand a E v1 ty1 l2 β2 ty2 ot T T':
    typed_write_end a E ot v1 ty1 l2 β2 ty2 T' -∗
    (∀ ty3, T' ty3 -∗ T ty3) -∗
    typed_write_end a E ot v1 ty1 l2 β2 ty2 T.
  Proof.
    iIntros "HT Hw Hl Hv". iMod ("HT" with "Hl Hv") as (?) "(?&HT)".
    iModIntro. iFrame. iSplit; [done|].
    iIntros "!> Hl". iMod ("HT" with "Hl") as (ty3) "(Hl&HT)".
    iExists _. iFrame. by iApply "Hw".
  Qed.

  Lemma fupd_typed_write_end a E v1 ty1 l2 β2 ty2 ot T:
    (|={E}=> typed_write_end a E ot v1 ty1 l2 β2 ty2 T)
    ⊢ typed_write_end a E ot v1 ty1 l2 β2 ty2 T.
  Proof. iIntros ">H". by iApply "H". Qed.

  (* TODO: can this be Global? *)
  Local Typeclasses Opaque typed_write_end.
  Global Instance elim_modal_fupd_typed_write_end P p a E v1 ty1 l2 β2 ty2 ot T:
    ElimModal True p false (|={E}=> P) P (typed_write_end a E ot v1 ty1 l2 β2 ty2 T) (typed_write_end a E ot v1 ty1 l2 β2 ty2 T).
  Proof.
    iIntros (?) "[HP HT]".
    rewrite bi.intuitionistically_if_elim -{2}fupd_typed_write_end.
    iMod "HP". by iApply "HT".
  Qed.

  Global Instance is_except_0_typed_write_end a E v1 ty1 l2 β2 ty2 ot T : IsExcept0 (typed_write_end a E ot v1 ty1 l2 β2 ty2 T).
  Proof. by rewrite /IsExcept0 -{2}fupd_typed_write_end -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_fupd_typed_write_end_atomic p E1 E2 v1 ty1 l2 β2 ty2 ot T P:
    ElimModal True p false
            (|={E1,E2}=> P) P
            (typed_write_end true E1 ot v1 ty1 l2 β2 ty2 T)
            (typed_write_end true E2 ot v1 ty1 l2 β2 ty2 (λ ty3, |={E2,E1}=> T ty3))%I
            | 100.
  Proof.
    iIntros (?) "[HP HT]". rewrite bi.intuitionistically_if_elim.
    iApply typed_write_end_mono_strong; [done|]. iIntros "Hv Hl". iMod "HP". iModIntro.
    iExists _, _, _, True%I. iFrame. iSplit; [done|].
    iApply (typed_write_end_wand with "(HT HP)").
    iIntros (ty3) "HT _ Hl". iMod "HT". iModIntro. iExists _. iFrame.
  Qed.

  Global Instance elim_acc_typed_write_end_atomic {X} E1 E2 α β γ v1 ty1 l2 β2 ty2 ot T :
    ElimAcc (X:=X) True
            (fupd E1 E2) (fupd E2 E1)
            α β γ
            (typed_write_end true E1 ot v1 ty1 l2 β2 ty2 T)
            (λ x, typed_write_end true E2 ot v1 ty1 l2 β2 ty2 (λ ty3, |={E2}=> β x ∗ (γ x -∗? T ty3)))%I | 100.
  Proof.
    iIntros (?) "Hinner Hacc".
    iMod "Hacc" as (x) "[Hα Hclose]".
    iApply (typed_write_end_wand with "(Hinner Hα)").
    iIntros (ty3) ">[Hβ HT]". iMod ("Hclose" with "Hβ"). by iApply "HT".
  Qed.
*)
End proper.
(*Global Typeclasses Opaque typed_read_end.
Global Typeclasses Opaque typed_write_end.*)

Definition FindLoc `{!typeG OK_ty Σ} {cs : compspecs} (l : address) :=
  {| fic_A := own_state * type; fic_Prop '(β, ty):= (l ◁ₗ{β} ty)%I; |}.
Definition FindVal `{!typeG OK_ty Σ} {cs : compspecs} cty (v : val) : @find_in_context_info assert :=
  {| fic_A := type; fic_Prop ty := ⎡v ◁ᵥₐₗ|cty| ty⎤%I; |}.
Definition FindValP {B : bi} (v : val) :=
  {| fic_A := B; fic_Prop P := P; |}.
Definition FindValOrLoc {Σ} (v : val) (l : address) :=
  {| fic_A := iProp Σ; fic_Prop P := P; |}.
Definition FindLocInBounds {Σ} (l : address) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Definition FindAllocAlive {Σ} (l : address) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindLoc FindVal FindValP FindValOrLoc FindLocInBounds FindAllocAlive.

(** setup instance generation *)
Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | typed_value ?cty ?x => constr:(TypedValue cty x)
  | typed_bin_op ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 => constr:(TypedBinOp x1 x2 x3 x4 x5 x6 x7 x8 x9)
  | typed_un_op ?x1 ?x2 ?x3 ?x4 ?x5 => constr:(TypedUnOp x1 x2 x3 x4 x5)
(*  | typed_call ?x1 ?x2 ?x3 ?x4 => constr:(TypedCall x1 x2 x3 x4)
  | typed_copy_alloc_id ?x1 ?x2 ?x3 ?x4 ?x5 => constr:(TypedCopyAllocId x1 x2 x3 x4 x5)
  | typed_place ?x1 ?x2 ?x3 ?x4 => constr:(TypedPlace x1 x2 x3 x4)
  | typed_read_end ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 => constr:(TypedReadEnd x1 x2 x3 x4 x5 x6 x7) *)
  | typed_write_end ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 => constr:(TypedWriteEnd x1 x2 x3 x4 x5 x6 x7 x8) 
  | typed_addr_of_end ?x1 ?x2 ?x3 => constr:(TypedAddrOfEnd x1 x2 x3)
(*   | typed_cas ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 => constr:(TypedCas x1 x2 x3 x4 x5 x6 x7) *)
  | typed_annot_expr ?x1 ?x2 ?x3 ?x4 => constr:(TypedAnnotExpr x1 x2 x3 x4)
(*   | typed_macro_expr ?x1 ?x2 => constr:(TypedMacroExpr x1 x2) *)
  | typed_if ?x1 ?x2 ?x3 ?x4 => constr:(TypedIf x1 x2 x3 x4)
(*   | typed_assert ?x1 ?x2 ?x3 => constr:(TypedAssert x1 x2 x3) *)
(*   | typed_switch ?x1 ?x2 ?x3 => constr:(TypedSwitch x1 x2 x3) *)
  | typed_annot_stmt ?x1 ?x2 ?x3 => constr:(TypedAnnotStmt x1 x2 x3)
  | copy_as ?x1 ?x2 ?x3 => constr:(CopyAs x1 x2 x3)
  | _ => fail "unknown judgement" c
  end.

Section typing.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Lemma find_in_context_type_loc_id l T:
    (∃ β ty, l ◁ₗ{β} ty ∗ T (β, ty))
    ⊢ find_in_context (FindLoc l) T.
  Proof. iDestruct 1 as (β ty) "[Hl HT]". iExists (_, _) => /=. iFrame. Qed.
  Definition find_in_context_type_loc_id_inst :=
    [instance find_in_context_type_loc_id with FICSyntactic].
  Global Existing Instance find_in_context_type_loc_id_inst | 1.

  Lemma find_in_context_type_val_id cty v T:
    (∃ ty, ⎡v ◁ᵥₐₗ|cty| ty⎤ ∗ T ty)
    ⊢ find_in_context (FindVal cty v) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Definition find_in_context_type_val_id_inst :=
    [instance find_in_context_type_val_id with FICSyntactic].
  Global Existing Instance find_in_context_type_val_id_inst | 1.

  Lemma find_in_context_type_val_P_id cty v T:
    (∃ ty, v ◁ᵥₐₗ|cty| ty ∗ T (v ◁ᵥₐₗ|cty| ty))
    ⊢ find_in_context (FindValP v) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists (ty_own_val ty _ _) => /=. iFrame. Qed.
  Definition find_in_context_type_val_P_id_inst :=
    [instance find_in_context_type_val_P_id with FICSyntactic].
  Global Existing Instance find_in_context_type_val_P_id_inst | 1.

  Lemma find_in_context_type_val_P_loc_id l T:
    (∃ β ty, l ◁ₗ{β} ty ∗ T (l ◁ₗ{β} ty))
    ⊢ find_in_context (FindValP l) T.
  Proof. iDestruct 1 as (β ty) "[Hl HT]". iExists (ty_own _ _ _) => /=. iFrame. Qed.
  Definition find_in_context_type_val_P_loc_id_inst :=
    [instance find_in_context_type_val_P_loc_id with FICSyntactic].
  Global Existing Instance find_in_context_type_val_P_loc_id_inst | 10.

  Lemma find_in_context_type_val_or_loc_P_id_val cty (v : val) (l : address) T:
    (∃ ty, v ◁ᵥₐₗ|cty| ty ∗ T (v ◁ᵥₐₗ|cty| ty))
    ⊢ find_in_context (FindValOrLoc v l) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists (ty_own_val ty _ _) => /=. iFrame. Qed.
  Definition find_in_context_type_val_or_loc_P_id_val_inst :=
    [instance find_in_context_type_val_or_loc_P_id_val with FICSyntactic].
  Global Existing Instance find_in_context_type_val_or_loc_P_id_val_inst | 1.

  Lemma find_in_context_type_val_or_loc_P_val_loc (lv l : address) T:
    (∃ β ty, lv ◁ₗ{β} ty ∗ T (lv ◁ₗ{β} ty))
    ⊢ find_in_context (FindValOrLoc lv l) T.
  Proof. iDestruct 1 as (β ty) "[Hl HT]". iExists _. by iFrame. Qed.
  Definition find_in_context_type_val_or_loc_P_val_loc_inst :=
    [instance find_in_context_type_val_or_loc_P_val_loc with FICSyntactic].
  Global Existing Instance find_in_context_type_val_or_loc_P_val_loc_inst | 10.

  Lemma find_in_context_type_val_or_loc_P_id_loc (v : val) (l : address) T:
    (∃ β ty, l ◁ₗ{β} ty ∗ T (l ◁ₗ{β} ty))
    ⊢ find_in_context (FindValOrLoc v l) T.
  Proof. iDestruct 1 as (β ty) "[Hl HT]". iExists (l ◁ₗ{β} ty)%I => /=. iFrame. Qed.
  Definition find_in_context_type_val_or_loc_P_id_loc_inst :=
    [instance find_in_context_type_val_or_loc_P_id_loc with FICSyntactic].
  Global Existing Instance find_in_context_type_val_or_loc_P_id_loc_inst | 20.

(*  Lemma find_in_context_loc_in_bounds l T :
    (∃ n, loc_in_bounds l n ∗ T (loc_in_bounds l n))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (n) "[??]". iExists (loc_in_bounds _ _) => /=. iFrame. Qed.
  Definition find_in_context_loc_in_bounds_inst :=
    [instance find_in_context_loc_in_bounds with FICSyntactic].
  Global Existing Instance find_in_context_loc_in_bounds_inst | 1.

  Lemma find_in_context_loc_in_bounds_loc l T :
    (∃ β ty, l ◁ₗ{β} ty ∗ T (l ◁ₗ{β} ty))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (β ty) "[??]". iExists (ty_own _ _ _) => /=. iFrame. Qed.
  Definition find_in_context_loc_in_bounds_loc_inst :=
    [instance find_in_context_loc_in_bounds_loc with FICSyntactic].
  Global Existing Instance find_in_context_loc_in_bounds_loc_inst | 10.

  Lemma find_in_context_alloc_alive_global l T :
    (alloc_global l ∗ T (alloc_global l))
    ⊢ find_in_context (FindAllocAlive l) T.
  Proof. iDestruct 1 as "?". iExists _ => /=. iFrame. Qed.
  Definition find_in_context_alloc_alive_global_inst :=
    [instance find_in_context_alloc_alive_global with FICSyntactic].
  Global Existing Instance find_in_context_alloc_alive_global_inst | 1.*)

  Lemma find_in_context_alloc_alive_loc l T :
    (∃ β ty, l ◁ₗ{β} ty ∗ T (l ◁ₗ{β} ty))
    ⊢ find_in_context (FindAllocAlive l) T.
  Proof. iDestruct 1 as (β ty) "[??]". iExists (ty_own _ _ _) => /=. iFrame. Qed.
  Definition find_in_context_alloc_alive_loc_inst :=
    [instance find_in_context_alloc_alive_loc with FICSyntactic].
  Global Existing Instance find_in_context_alloc_alive_loc_inst | 10.

  Global Instance related_to_loc A l β ty : RelatedTo (λ x : A, l ◁ₗ{β x} ty x)%I | 100
    := {| rt_fic := FindLoc l |}.
  Global Instance related_to_val A cty v ty : RelatedTo (λ x : A, (valinject cty v) ◁ᵥ|cty| ty x)%I | 100
    := {| rt_fic := FindValP v |}.
(*  Global Instance related_to_loc_in_bounds A l n : RelatedTo (λ x : A, loc_in_bounds l (n x)) | 100
    := {| rt_fic := FindLocInBounds l |}.
  Global Instance related_to_alloc_alive A l : RelatedTo (λ x : A, alloc_alive_loc l) | 100
    := {| rt_fic := FindAllocAlive l |}.

  Global Program Instance learnalignment_none β ty : LearnAlignment β ty None | 1000.
  Next Obligation. iIntros (???) "?". done. Qed.

  Lemma subsume_loc_in_bounds A ty β l (n m : nat) `{!LocInBounds ty β m} T :
    (l ◁ₗ{β} ty -∗ ⌜n ≤ m⌝ ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} ty) (λ x : A, loc_in_bounds l n) T.
  Proof.
    iIntros "HT Hl".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#?".
    iDestruct ("HT" with "Hl") as (??) "?". iExists _. iFrame.
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.
  Definition subsume_loc_in_bounds_inst := [instance subsume_loc_in_bounds].
  Global Existing Instance subsume_loc_in_bounds_inst | 10.

  Lemma subsume_loc_in_bounds_evar A ty β l (n : A → nat) (m : nat)
    `{!LocInBounds ty β m} T :
    (l ◁ₗ{β} ty -∗ ∃ x, ⌜n x = m⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ty) (λ x, loc_in_bounds l (n x)) T.
  Proof.
    iIntros "HT Hl".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#?".
    iDestruct ("HT" with "Hl") as (??) "?". iExists _. iFrame.
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.
  Definition subsume_loc_in_bounds_evar_inst := [instance subsume_loc_in_bounds_evar].
  Global Existing Instance subsume_loc_in_bounds_evar_inst | 20.

  Lemma subsume_alloc_alive_global A l T :
    (∃ x, T x)
    ⊢ subsume (alloc_global l) (λ x : A, alloc_alive_loc l) T.
  Proof. iIntros "[% ?] Hl". iExists _. iFrame. by iApply (alloc_global_alive). Qed.
  Definition subsume_alloc_alive_global_inst := [instance subsume_alloc_alive_global].
  Global Existing Instance subsume_alloc_alive_global_inst.

  Lemma subsume_alloc_alive A ty β l P `{!AllocAlive ty β P} T :
    (* You don't get l ◁ₗ{β} ty back because alloc_alive is not persistent. *)
    (P ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} ty) (λ x : A, alloc_alive_loc l) T.
  Proof. iIntros "[HP [% ?]] Hl". iExists _. iFrame. by iApply (alloc_alive_alive with "HP"). Qed.
  Definition subsume_alloc_alive_inst := [instance subsume_alloc_alive].
  Global Existing Instance subsume_alloc_alive_inst | 5.

  Lemma subsume_alloc_alive_type_alive A ty β l `{!CheckOwnInContext (type_alive ty β)} T :
    (type_alive ty β ∗ ∃ x, T x)
    ⊢ subsume (l ◁ₗ{β} ty) (λ x : A, alloc_alive_loc l) T.
  Proof. iIntros "[Ha [% ?]] Hl". rewrite /type_alive. iExists _. iFrame. by iApply "Ha". Qed.
  Definition subsume_alloc_alive_type_alive_inst := [instance subsume_alloc_alive_type_alive].
  Global Existing Instance subsume_alloc_alive_type_alive_inst | 10.

  Lemma simplify_goal_type_alive ty β P `{!AllocAlive ty β P} T :
    □ P ∗ T
    ⊢ simplify_goal (type_alive ty β) T.
  Proof.
    iIntros "[#HP HT]". iFrame. rewrite /type_alive. iIntros "!>" (?) "Hl".
      by iApply (alloc_alive_alive with "HP Hl").
  Qed.
  Definition simplify_goal_type_alive_inst := [instance simplify_goal_type_alive with 0%N].
  Global Existing Instance simplify_goal_type_alive_inst.

  Lemma subsume_loc_in_bounds_leq A (l : loc) (n1 n2 : nat) T :
    (⌜n2 ≤ n1⌝%nat ∗ ∃ x, T x)
    ⊢ subsume (loc_in_bounds l n1) (λ x : A, loc_in_bounds l n2) T.
  Proof. iIntros "[% [% ?]] #?". iExists _. iFrame. by iApply loc_in_bounds_shorten. Qed.
  Definition subsume_loc_in_bounds_leq_inst := [instance subsume_loc_in_bounds_leq].
  Global Existing Instance subsume_loc_in_bounds_leq_inst | 10.

  Lemma subsume_loc_in_bounds_leq_evar A (l : loc) (n1 : nat) (n2 : A → nat) T :
    (∃ x, ⌜n2 x = n1⌝%nat ∗ T x)
    ⊢ subsume (loc_in_bounds l n1) (λ x, loc_in_bounds l (n2 x)) T.
  Proof. iIntros "[% [% ?]] #?". iExists _. iFrame. iApply loc_in_bounds_shorten; [|done]. lia. Qed.
  Definition subsume_loc_in_bounds_leq_evar_inst := [instance subsume_loc_in_bounds_leq_evar].
  Global Existing Instance subsume_loc_in_bounds_leq_evar_inst | 20.*)

  Lemma apply_subsume_place_true l1 β1 ty1 l2 β2 ty2:
    l1 ◁ₗ{β1} ty1 -∗
    subsume (l1 ◁ₗ{β1} ty1) (λ _ : unit, l2 ◁ₗ{β2} ty2) (λ _, emp) -∗
    l2 ◁ₗ{β2} ty2.
  Proof. iIntros "Hl1 Hsub". iDestruct ("Hsub" with "Hl1") as (?) "[$ _]". Qed.

  Lemma apply_subsume_place l ty2 T:
    (find_in_context (FindDirect (λ '(β, ty), l◁ₗ{β}ty)) (λ '(β, ty),
         subsume (l◁ₗ{β} ty) (λ _ : unit, l◁ₗ{β} ty2) (λ _, l◁ₗ{β}ty2 -∗ T))) -∗ T.
  Proof.
    iDestruct 1 as ([β ty1]) "[Hl Hsub]".
    iDestruct ("Hsub" with "Hl") as (?) "[Hl HT]". by iApply "HT".
  Qed.

  Lemma simplify_place_refine_l A (ty : rtype A) l β T:
    (∀ x, l ◁ₗ{β} x @ ty -∗ T) ⊢ simplify_hyp (l◁ₗ{β}ty) T.
  Proof.
    iIntros "HT Hl". unfold ty_of_rty; simpl_type. iDestruct "Hl" as (x) "Hv". by iApply "HT".
  Qed.
  Definition simplify_place_refine_l_inst := [instance simplify_place_refine_l with 0%N].
  Global Existing Instance simplify_place_refine_l_inst.

  Lemma simplify_val_refine_l A (ty : rtype A) cty v T:
    (∀ x, v ◁ᵥₐₗ|cty| (x @ ty) -∗ T) ⊢ simplify_hyp (v ◁ᵥₐₗ|cty| ty) T.
  Proof.
    iIntros "HT Hl". unfold ty_of_rty; simpl_type. iDestruct "Hl" as (x) "Hv". by iApply "HT".
  Qed.
  Definition simplify_val_refine_l_inst := [instance simplify_val_refine_l with 0%N].
  Global Existing Instance simplify_val_refine_l_inst.

  (* This is forced since it can create evars in places where we don't
  want them. We might first want to try subtyping without the evar (see e.g. optional ) *)
  Lemma simplify_goal_place_refine_r A (ty : rtype A) l β T:
    (∃ x, l ◁ₗ{β} x @ ty ∗ T) ⊢ simplify_goal (l◁ₗ{β}ty) T.
  Proof. iDestruct 1 as (x) "[Hl $]". by iExists _. Qed.
  Definition simplify_goal_place_refine_r_inst := [instance simplify_goal_place_refine_r with 10%N].
  Global Existing Instance simplify_goal_place_refine_r_inst.

  Lemma simplify_goal_val_refine_r A (ty : rtype A) cty v T :
    (∃ x, v ◁ᵥₐₗ|cty| (x @ ty) ∗ T) ⊢ simplify_goal (v ◁ᵥₐₗ|cty| ty) T.
  Proof. iDestruct 1 as (x) "[? $]". by iExists _. Qed.
  Definition simplify_goal_val_refine_r_inst := [instance simplify_goal_val_refine_r with 10%N].
  Global Existing Instance simplify_goal_val_refine_r_inst.

  (* This rule is complete as [LocInBounds] implies that the location cannot be NULL. *)
(*  Lemma simplify_goal_NULL_loc_in_bounds β ty n `{!LocInBounds ty β n} T:
    False
    ⊢ simplify_goal (NULL_loc ◁ₗ{β} ty) T.
  Proof. by iIntros (?). Qed.
  Definition simplify_goal_NULL_loc_in_bounds_inst := [instance simplify_goal_NULL_loc_in_bounds with 0%N].
  Global Existing Instance simplify_goal_NULL_loc_in_bounds_inst.*)

  Global Instance simple_subsume_place_id ty : SimpleSubsumePlace ty ty emp | 1.
  Proof. iIntros (??) "_ $". Qed.
  Global Instance simple_subsume_val_id cty ty : SimpleSubsumeVal cty ty ty emp | 1.
  Proof. iIntros (?) "_ $". Qed.
  Global Instance simple_subsume_place_refinement_id A ty (x1 x2 : A) :
    SimpleSubsumePlace (x1 @ ty) (x2 @ ty) (<affine> ⌜x1 = x2⌝) | 100.
  Proof. iIntros (?? ->) "$". Qed.
  Global Instance simple_subsume_val_refinement_id A cty ty (x1 x2 : A) :
    SimpleSubsumeVal cty (x1 @ ty) (x2 @ ty) (<affine> ⌜x1 = x2⌝) | 100.
  Proof. iIntros (? ->) "$". Qed.

  Global Instance simple_subsume_place_rty_to_ty_l A (ty1 : rtype A) P `{!∀ x, SimpleSubsumePlace (x @ ty1) ty2 P} :
    SimpleSubsumePlace ty1 ty2 P.
  Proof.
    iIntros (l β) "HP Hl". unfold ty_of_rty; simpl_type. iDestruct "Hl" as (x) "Hl".
    iApply (@simple_subsume_place with "HP Hl").
  Qed.
  Global Instance simple_subsume_place_rty_to_ty_r A (ty1 ty2 : rtype A) x P `{!SimpleSubsumePlace (x @ ty1) (x @ ty2) P} :
    SimpleSubsumePlace (x @ ty1) ty2 P.
  Proof. iIntros (l β) "HP Hl". iExists (x). iApply (@simple_subsume_place with "HP Hl"). Qed.

  Lemma simple_subsume_place_to_subsume A l β ty1 ty2 P
    `{!∀ x, SimpleSubsumePlace ty1 (ty2 x) (P x)} T:
    (∃ x, P x ∗ T x) ⊢ subsume (l ◁ₗ{β} ty1) (λ x : A, l ◁ₗ{β} ty2 x) T.
  Proof. iIntros "[% [HP ?]] Hl". iExists _. iFrame. iApply (@simple_subsume_place with "HP Hl"). Qed.
  Definition simple_subsume_place_to_subsume_inst := [instance simple_subsume_place_to_subsume].
  Global Existing Instance simple_subsume_place_to_subsume_inst.

  Lemma simple_subsume_val_to_subsume A cty v ty1 ty2 P `{!∀ x, SimpleSubsumeVal cty ty1 (ty2 x) (P x)} T:
    (∃ x, P x ∗ T x) ⊢ subsume (v ◁ᵥₐₗ|cty| ty1) (λ x : A, v ◁ᵥₐₗ|cty| ty2 x) T.
  Proof. iIntros "[% [HP ?]] Hv". iExists _. iFrame. iApply (@simple_subsume_val with "HP Hv"). Qed.
  Definition simple_subsume_val_to_subsume_inst := [instance simple_subsume_val_to_subsume].
  Global Existing Instance simple_subsume_val_to_subsume_inst.

  Lemma subsume_place_own_ex A ty1 ty2 l β1 β2 T:
    subsume (l ◁ₗ{β1} ty1) (λ x : A, l ◁ₗ{β2 x} ty2 x) T :-
      inhale (l ◁ₗ{β1} ty1); ∃ x, exhale (<affine> ⌜β2 x = β1⌝); exhale (l ◁ₗ{β2 x} ty2 x); return T x.
  Proof. iIntros "HT Hl". iDestruct ("HT" with "Hl") as "[% [<- [??]]]". iExists _. iFrame. Qed.
  (* This lemma is applied via Hint Extern instead of declared as an instance with a `{!∀ x,
  IsEx (β x)} precondition for better performance. *)
  Definition subsume_place_own_ex_inst := [instance subsume_place_own_ex].

  Lemma subsume_place_ty_ex A ty1 ty2 l β T:
    subsume (l ◁ₗ{β} ty1) (λ x : A, l ◁ₗ{β} ty2 x) T :-
      ∃ x, exhale (<affine> ⌜ty2 x = ty1⌝); return T x.
  Proof. iIntros "[% [<- ?]] ?". iExists _. iFrame. Qed.
  (* This lemma is applied via Hint Extern instead of declared as an instance with a `{!∀ x,
  IsEx (ty2 x)} precondition for better performance. *)
  Definition subsume_place_ty_ex_inst := [instance subsume_place_ty_ex].

  Lemma subtype_var {A B} (ty : A → type) x y l β T:
    (∃ z, <affine> ⌜x = y z⌝ ∗ T z)
    ⊢ subsume (l ◁ₗ{β} ty x) (λ z : B, l ◁ₗ{β} ty (y z)) T.
  Proof. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  (* This must be an Hint Extern because an instance would be a big slowdown. *)
  Definition subtype_var_inst := [instance @subtype_var].

  Lemma typed_binop_simplify ge v1 P1 v2 P2 o1 o2 ot1 ot2 ot {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} `{!TCOneIsSome o1 o2} op T:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_bin_op ge v1 P v2 P2 op ot1 ot2 ot T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_bin_op ge v1 P1 v2 P op ot1 ot2 ot T))).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then G2 else G1
     | Some n1, _ => G1
     | _, _ => G2
       end in
    G
    ⊢ typed_bin_op ge v1 P1 v2 P2 op ot1 ot2 ot T.
  Proof.
    iIntros "/= Hs Hv1 Hv2".
    destruct o1 as [n1|], o2 as [n2|] => //. 1: case_match.
    1,3,4: iDestruct (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    4,5,6: iDestruct (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$]").
  Qed.
  Definition typed_binop_simplify_inst := [instance typed_binop_simplify].
  Global Existing Instance typed_binop_simplify_inst | 1000.

(*  Lemma typed_binop_comma v1 v2 P (ty : type) ot1 ot2 T:
    (P -∗ T v2 ty)
    ⊢ typed_bin_op v1 P v2 (v2 ◁ᵥ ty) Comma ot1 ot2 T.
  Proof.
    iIntros "HT H1 H2" (Φ) "HΦ". iApply (wp_binop_det_pure v2).
    { split; [ by inversion 1 | move => ->; constructor ]. }
    iDestruct ("HT" with "H1") as "HT". iApply ("HΦ" $! v2 ty with "H2 HT").
  Qed.
  Definition typed_binop_comma_inst := [instance typed_binop_comma].
  Global Existing Instance typed_binop_comma_inst. *)

  Lemma typed_unop_simplify v P n t cty {SH : SimplifyHyp P (Some n)} op T:
    (SH (find_in_context (FindValP v) (λ P, typed_un_op v P op t cty T))).(i2p_P)
    ⊢ typed_un_op v P op t cty T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as (P') "[Hv Hsub]". simpl in *. by iApply ("Hsub" with "[$]").
  Qed.
  Definition typed_unop_simplify_inst := [instance typed_unop_simplify].
  Global Existing Instance typed_unop_simplify_inst | 1000.

(*  Lemma typed_copy_alloc_id_simplify v1 P1 v2 P2 o1 o2 ot {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} `{!TCOneIsSome o1 o2} T:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_copy_alloc_id v1 P v2 P2 ot T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_copy_alloc_id v1 P1 v2 P ot T))).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then G2 else G1
     | Some n1, _ => G1
     | _, _ => G2
       end in
    G
    ⊢ typed_copy_alloc_id v1 P1 v2 P2 ot T.
  Proof.
    iIntros "/= Hs Hv1 Hv2".
    destruct o1 as [n1|], o2 as [n2|] => //. 1: case_match.
    1,3,4: iDestruct (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    4,5,6: iDestruct (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$]").
  Qed.
  Definition typed_copy_alloc_id_simplify_inst := [instance typed_copy_alloc_id_simplify].
  Global Existing Instance typed_copy_alloc_id_simplify_inst | 1000.

  Lemma typed_cas_simplify v1 P1 v2 P2 v3 P3 ot o1 o2 o3 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} {SH3 : SimplifyHyp P3 o3} `{!TCOneIsSome3 o1 o2 o3} T:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_cas ot v1 P v2 P2 v3 P3 T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_cas ot v1 P1 v2 P v3 P3 T))).(i2p_P) in
    let G3 := (SH3 (find_in_context (FindValP v3) (λ P, typed_cas ot v1 P1 v2 P2 v3 P T))).(i2p_P) in
    let min o1 o2 :=
       match o1.1, o2.1 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then o2 else o1
     | Some n1, _ => o1
     | _, _ => o2
       end in
    let G := (min (o1, G1) (min (o2, G2) (o3, G3))).2 in
    G
    ⊢ typed_cas ot v1 P1 v2 P2 v3 P3 T.
  Proof.
    iIntros "/= Hs Hv1 Hv2 Hv3".
    destruct o1 as [n1|], o2 as [n2|], o3 as [n3|] => //=; repeat case_match => /=.
    all: try iDestruct (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    all: try iDestruct (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: try iDestruct (i2p_proof with "Hs Hv3") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$] [$]").
  Qed.
  Definition typed_cas_simplify_inst := [instance typed_cas_simplify].
  Global Existing Instance typed_cas_simplify_inst | 1000.*)

  Lemma typed_annot_stmt_simplify A (a : A) l P n {SH : SimplifyHyp P (Some n)} T:
    (SH (find_in_context (FindLoc l) (λ '(β1, ty1),
       typed_annot_stmt a l (l ◁ₗ{β1} ty1) T))).(i2p_P)
    ⊢ typed_annot_stmt a l P T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as ([β1 ty1]) "[Hl Hannot]" => /=.
      by iApply ("Hannot" with "[$]").
  Qed.
  Definition typed_annot_stmt_simplify_inst := [instance typed_annot_stmt_simplify].
  Global Existing Instance typed_annot_stmt_simplify_inst | 1000.

  Lemma typed_annot_expr_simplify A m (a : A) v P n {SH : SimplifyHyp P (Some n)} T:
    (SH (find_in_context (FindValP v) (λ Q,
       typed_annot_expr m a v Q T))).(i2p_P)
    ⊢ typed_annot_expr m a v P T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as ([β1 ty1]) "[Hl Hannot]" => /=.
      by iApply ("Hannot" with "[$]").
  Qed.
  Definition typed_annot_expr_simplify_inst := [instance typed_annot_expr_simplify].
  Global Existing Instance typed_annot_expr_simplify_inst | 1000.

  Lemma typed_if_simplify ot v (P F : iProp Σ) n {SH : SimplifyHyp P (Some n)} T1 T2:
    (SH (find_in_context (FindValP v) (λ Q,
       typed_if ot v Q F T1 T2))).(i2p_P)
    ⊢ typed_if ot v P F T1 T2.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as (Q) "[HQ HT]" => /=. simpl in *.
    iApply ("HT" with "HQ").
  Qed.
  Definition typed_if_simplify_inst := [instance typed_if_simplify].
  Global Existing Instance typed_if_simplify_inst | 1000.

(*  Lemma typed_assert_simplify ot v P n {SH : SimplifyHyp P (Some n)} s fn ls R Q:
    (SH (find_in_context (FindValP v) (λ P',
       typed_assert ot v P' s fn ls R Q))).(i2p_P)
    ⊢ typed_assert ot v P s fn ls R Q.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as (P') "[HP' HT]" => /=. simpl in *.
    iApply ("HT" with "HP'").
  Qed.
  Definition typed_assert_simplify_inst := [instance typed_assert_simplify].
  Global Existing Instance typed_assert_simplify_inst | 1000. *)

  (*** statements *)

  Global Instance elim_modal_bupd_typed_stmt p Espec ge s f R P :
    ElimModal True%type p false (|==> P) P (typed_stmt Espec ge s f R) (typed_stmt Espec ge s f R).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd ⊤) fupd_frame_r bi.wand_elim_r.
    iIntros "_ Hs". iMod "Hs". by iApply "Hs".
  Qed.

  Global Instance elim_modal_fupd_typed_stmt p Espec ge s f R P :
    ElimModal True%type p false (|={⊤}=> P) P (typed_stmt Espec ge s f R) (typed_stmt Espec ge s f R).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r.
    iIntros "_ Hs". iMod "Hs". by iApply "Hs".
  Qed.

(*  Lemma type_goto Q b fn ls R s:
    Q !! b = Some s →
    typed_stmt s fn ls R Q
    ⊢ typed_stmt (Sgoto b) fn ls R Q.
  Proof.
    iIntros (HQ) "Hs". iIntros (Hls). iApply wps_goto => //.
    iModIntro. by iApply "Hs".
  Qed.

  Lemma type_goto_precond P Q b fn ls R:
    (typed_block P b fn ls R Q ∗ P ∗ True)
    ⊢ typed_stmt (Goto b) fn ls R Q.
  Proof.
    iIntros "[Hblock [HP _]]" (Hls).
    by iApply "Hblock".
  Qed.

*)

  (* Ke: possible way to handle cast: dispatch type checking rules to 
     type_Ecast, and only cover cases where it doesn't need memory.
     similar to lithium.theories.typing.int, have one rule for each 
     concrete (t1, t2) in (Ecast t1 t2) *)
  Lemma type_assign Espec ge f e1 e2 (T: option val -> type -> assert):
    type_is_by_value (typeof e1) = true ->
    type_is_volatile (typeof e1) = false ->
    typed_val_expr ge f (Ecast e2 (typeof e1)) (λ v ty,
      <affine> ⌜tc_val' (typeof e1) v⌝ ∗
       typed_write ge f false e1 (typeof e1) v ty (T None tytrue))
    ⊢ typed_stmt Espec ge (Sassign e1 e2) f T.
  Proof.
    intros.
    unfold typed_stmt.
    rewrite -wp_store.
    iIntros "H". iApply "H".
    iIntros (v ty) "H (% & ty_write)".
    iSplit; [done|].
    iApply wp_lvalue_mono.
    { intros; apply derives_refl. }
    iApply "ty_write".
    iIntros ((b, o)) "upd".
    iMod ("upd" with "H") as "(%Hot & Hl & upd)"; iModIntro.
    iExists Tsh.
    iSplit; [auto|].
    rewrite mapsto_layout_iff_mapsto_and_layout.
    iDestruct "Hl" as (v_rep) "[%Hl ↦]".
    iSplitR "upd".
    - rewrite /mapsto 
      -mapsto_mapsto_ /adr2val /=.
      rewrite by_value_data_at_rec_nonvolatile //.
    - iIntros "!> l↦".
      iMod ("upd" with "[l↦]"); try done.
      rewrite /mapsto /mapsto_ /adr2val /=.
      rewrite by_value_data_at_rec_nonvolatile //.
      rewrite repinject_valinject //.
  Qed.

  (* sets any v' to v *)
  Lemma type_set Espec ge f (id:ident) e v' (T: option val -> type -> assert):
    typed_val_expr ge f e (λ v ty, <affine> ⌜v ≠ Vundef⌝ ∗ env.temp id v' ∗ 
                            (⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ env.temp id v -∗ T None tytrue))%I
      ⊢ typed_stmt Espec ge (Sset id e) f T.
  Proof.
    iIntros "He".
    iApply wp_set.
    iApply "He".
    iIntros (??) "v_ty (% & $ & H)".
    rewrite /typed_stmt_post_cond /RA_normal.
    iModIntro.
    iIntros "?".
    iApply ("H" with "[$]"); try done.
  Qed.

  Lemma type_return_some Espec ge f e (T : option val → type -> assert):
    cast_pointer_to_bool (typeof e) (fn_return f) = false ->
    (typed_val_expr ge f e (λ v ty, ⌜tc_val (typeof e) v⌝ ∧ ⌜Clight_Cop2.sem_cast (typeof e) (fn_return f) v = Some v⌝ ∧
                                T (Some v) ty)
    ⊢ typed_stmt Espec ge (Sreturn $ Some e) f T).
  Proof.
    intros.
    unfold typed_stmt.
    iIntros "H".
    iApply wp_return.
    simpl.
    iApply wp_cast; first done.
    iApply "H". 
    iIntros (v ty) "H1 (H2 & (%H3 & H4))".
    iFrame.
    iPureIntro.
    split; auto.
  Qed.

  Lemma type_return_none Espec ge f (T : option val → type -> assert) cty ty:
    ⎡Vundef ◁ᵥₐₗ|cty| ty⎤ ∗ T (Some Vundef) ty
    ⊢ typed_stmt Espec ge (Sreturn $ None) f T.
  Proof.
    unfold typed_stmt.
    iIntros "H".
    iApply wp_return.
    simpl. iFrame.
  Qed.

  Lemma type_if Espec ge f e s1 s2 R:
    typed_val_expr ge f e (λ v ty, typed_if (typeof e) v ⎡v ◁ᵥₐₗ|typeof e| ty⎤
          (⎡valid_val v⎤) (typed_stmt Espec ge s1 f R) (typed_stmt Espec ge s2 f R))
    ⊢ typed_stmt Espec ge (Sifthenelse e s1 s2) f R.
  Proof.
    iIntros "He".
    iApply wp_if.
    iApply "He". iIntros (v ty) "Hv Hs".
    iDestruct ("Hs" with "Hv") as "Hs".
    (* rewrite -bi.and_assoc.
    iDestruct "Hs" as "[%H Hs]".  *)
    iSplit; [iDestruct "Hs" as "[$ _]"; done | iDestruct "Hs" as "[_ Hs]"].
    destruct (typeof e) eqn: Ht; iDestruct "Hs" as (b Hv) "Hs"; try done; try (iFrame; done).
    - destruct v; try done.
      iFrame.
      simpl in *.
      destruct (Int.eq i0 Int.zero) eqn: Heq.
      + apply Int.same_if_eq in Heq as ->.
        destruct s; inv Hv; done.
      + case_bool_decide; try done.
        subst; destruct s; inv Hv.
        * apply (val_lemmas.signed_inj _ Int.zero) in H0 as ->.
          rewrite Int.eq_true // in Heq.
        * apply (client_lemmas.unsigned_eq_eq _ Int.zero) in H0 as ->.
          rewrite Int.eq_true // in Heq.
    - destruct v; try done.
      iFrame.
      simpl in *.
      destruct (Int64.eq i Int64.zero) eqn: Heq.
      + apply Int64.same_if_eq in Heq as ->.
        destruct s; inv Hv; done.
      + case_bool_decide; try done.
        subst; destruct s; inv Hv.
        * apply (signed_inj_64 _ Int64.zero) in H0 as ->.
          rewrite Int64.eq_true // in Heq.
        * apply (unsigned_inj_64 _ Int64.zero) in H0 as ->.
          rewrite Int64.eq_true // in Heq.
Qed.

(*  Lemma type_switch Q it e m ss def fn ls R:
    typed_val_expr e (λ v ty, typed_switch v ty it m ss def fn ls R Q)
    ⊢ typed_stmt (Switch it e m ss def) fn ls R Q.
  Proof.
    iIntros "He" (Hls).
    have -> : (Switch it e m ss def) = (W.to_stmt (W.Switch it (W.Expr e) m (W.Stmt <$> ss) (W.Stmt def)))
      by rewrite /W.to_stmt/= -!list_fmap_compose list_fmap_id.
    iApply tac_wps_bind; first done.
    rewrite /W.to_expr /W.to_stmt /= -list_fmap_compose list_fmap_id.

    iApply "He". iIntros (v ty) "Hv Hs".
    iDestruct ("Hs" with "Hv") as (z Hn) "Hs".
    iAssert (⌜∀ i : nat, m !! z = Some i → is_Some (ss !! i)⌝%I) as %?. {
      iIntros (i ->). iDestruct "Hs" as (s ->) "_"; by eauto.
    }
    iApply wps_switch; [done|done|..].
    destruct (m !! z) => /=.
    - iDestruct "Hs" as (s ->) "Hs". by iApply "Hs".
    - by iApply "Hs".
  Qed.

  Lemma type_assert Q ot e s fn ls R:
    typed_val_expr e (λ v ty, typed_assert ot v (v ◁ᵥ ty) s fn ls R Q)
    ⊢ typed_stmt (assert{ot}: e; s) fn ls R Q.
  Proof.
    iIntros "He" (Hls). wps_bind.
    iApply "He". iIntros (v ty) "Hv Hs".
    iDestruct ("Hs" with "Hv") as "Hs".
    destruct ot => //.
    - iDestruct "Hs" as (???) "Hs".
      iApply wps_assert_bool; [done|done|..]. by iApply "Hs".
    - iDestruct "Hs" as (???) "Hs".
      iApply wps_assert_int; [done|done|..]. by iApply "Hs".
    - iDestruct "Hs" as (???) "[Hpre Hs]".
      iApply (wps_assert_ptr with "Hpre"); [done..|]. by iApply "Hs".
  Qed.

  Lemma type_exprs s e fn ls R Q:
    (typed_val_expr e (λ v ty, v ◁ᵥ ty -∗ typed_stmt s fn ls R Q))
    ⊢ typed_stmt (ExprS e s) fn ls R Q.
  Proof.
    iIntros "Hs ?". wps_bind. iApply "Hs". iIntros (v ty) "Hv Hs".
    iApply wps_exprs. iApply step_fupd_intro => //. iModIntro.
    by iApply ("Hs" with "Hv").
  Qed.

  Lemma type_skips Espec Delta s R:
    (|={⊤}[∅]▷=> typed_stmt Espec Delta s R) ⊢ typed_stmt (Sskip s) fn ls R Q.
  Proof.
    iIntros "Hs ?". iApply wps_skip. iApply (step_fupd_wand with "Hs"). iIntros "Hs". by iApply "Hs".
  Qed.

  Lemma type_skips' s fn ls Q R:
    typed_stmt s fn ls R Q ⊢ typed_stmt (SkipS s) fn ls R Q.
  Proof. iIntros "Hs". iApply type_skips. by iApply step_fupd_intro. Qed.

  Lemma type_annot_stmt {A} p (a : A) s fn ls Q R:
    (typed_addr_of p (λ l β ty, typed_annot_stmt a l (l ◁ₗ{β} ty) (typed_stmt s fn ls R Q)))
    ⊢ typed_stmt (annot: a; expr: &p; s) fn ls R Q.
  Proof.
    iIntros "Hs ?". iApply wps_annot => /=.
    wps_bind. rewrite /AddrOf. iApply "Hs".
    iIntros (l β ty) "Hl Ha". iApply wps_exprs.
      by iApply ("Ha" with "Hl").
  Qed.

  Lemma type_annot_stmt_assert {A} P id s fn ls R Q:
    (∃ a : A, P a ∗ (P a -∗ (typed_stmt s fn ls R Q)))
    ⊢ typed_stmt (annot: (AssertAnnot id); s) fn ls R Q.
  Proof. iIntros "[%a [HP Hcont]] ?". iApply wps_annot => /=. by iApply ("Hcont" with "HP"). Qed.

  Lemma typed_block_rec Ps Q fn ls R s:
    ([∗ map] b ↦ P ∈ Ps, ∃ s, ⌜Q !! b = Some s⌝ ∗ □(([∗ map] b ↦ P ∈ Ps, typed_block P b fn ls R Q) -∗ P -∗ typed_stmt s fn ls R Q)) -∗
    (([∗ map] b ↦ P ∈ Ps, typed_block P b fn ls R Q) -∗ typed_stmt s fn ls R Q) -∗
    typed_stmt s fn ls R Q.
  Proof.
    iIntros "HQ Hs" (Hls).
    iApply ("Hs" with "[HQ]"); last done.
    iApply wps_block_rec.
    iApply (big_sepM_mono with "HQ").
    move => b P Hb /=.
    repeat f_equiv. iIntros "Hs". by iApply "Hs".
  Qed.*)

  (*** expressions *)
  Lemma type_val_context cty v T:
    (find_in_context (FindVal cty v) T)
    ⊢ typed_value cty v T.
  Proof.
    iDestruct 1 as (ty) "[Hv HT]". simpl in *.
    iExists _. iFrame.
  Qed.
  Definition type_val_context_inst := [instance type_val_context].
  Global Existing Instance type_val_context_inst | 100.

  Lemma type_const_int ge f i T t:
    typed_value t (Vint i) (T (Vint i))
    ⊢ typed_val_expr ge f (Econst_int i t) T.
  Proof.
    iIntros "HP" (Φ) "HΦ".
    iDestruct "HP" as (ty) "[Hv HT]".
    iApply wp_const_int. iApply ("HΦ" with "[Hv] HT").
    rewrite /typeof //.
  Qed.

  Lemma type_const_long ge f i t T:
    typed_value t (Vlong i) (T (Vlong i))
    ⊢ typed_val_expr ge f (Econst_long i t) T.
  Proof.
    iIntros "HP" (Φ) "HΦ".
    iDestruct "HP" as (ty) "[Hv HT]".
    by iApply wp_const_long; iApply ("HΦ" with "[$]").
  Qed.

  Lemma type_const_float ge f i t T:
    typed_value t (Vfloat i) (T (Vfloat i))
    ⊢ typed_val_expr ge f (Econst_float i t) T.
  Proof.
    iIntros "HP" (Φ) "HΦ".
    iDestruct "HP" as (ty) "[Hv HT]".
    by iApply wp_const_float; iApply ("HΦ" with "[$]").
  Qed.

  Lemma type_const_single ge f i t T:
    typed_value t (Vsingle i) (T (Vsingle i))
    ⊢ typed_val_expr ge f (Econst_single i t) T.
  Proof.
    iIntros "HP" (Φ) "HΦ".
    iDestruct "HP" as (ty) "[Hv HT]".
    by iApply wp_const_single; iApply ("HΦ" with "[$]").
  Qed.


  Lemma type_bin_op ge f o e1 e2 ot T:
    typed_val_expr ge f e1 (λ v1 ty1,
      typed_val_expr ge f e2 (λ v2 ty2,
        typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|typeof e1| ty1⎤ 
                        v2 ⎡v2 ◁ᵥₐₗ|typeof e2| ty2⎤ o (typeof e1) (typeof e2) ot T))
    ⊢ typed_val_expr ge f (Ebinop o e1 e2 ot) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    iApply wp_binop_rule. iApply "He1". iIntros (v1 ty1) "Hv1 He2".
    iApply "He2". iIntros (v2 ty2) "Hv2 Hop".
    by iApply ("Hop" with "Hv1 Hv2").
  Qed.

  Lemma type_un_op ge f o e ot T:
    typed_val_expr ge f e (λ v ty, typed_un_op v ⎡v ◁ᵥₐₗ|typeof e| ty⎤ o (typeof e) ot T)
    ⊢ typed_val_expr ge f (Eunop o e ot) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    iApply wp_unop_rule. iApply "He". iIntros (v ty) "Hv Hop".
    by iApply ("Hop" with "Hv").
  Qed.

  Lemma type_tempvar ge f _x v cty T ty:
     env.temp _x v ∗ (env.temp _x v -∗ ⎡v ◁ᵥₐₗ|cty| ty⎤ ∗ T v ty)
    ⊢ typed_val_expr ge f (Etempvar _x cty) T.
  Proof.
    iIntros "(Hx & HT)" (Φ) "HΦ".
    iApply wp_tempvar_local.
    iFrame.
    iIntros "Hx".
    iDestruct ("HT" with "Hx") as "(Hv & HT)".
    iApply ("HΦ" with "[$]"). done.
  Qed.

  Lemma type_var_local ge f _x b β ty c_ty (T: address -> own_state -> type -> assert) :
    env.lvar _x c_ty b ∗
    (env.lvar _x c_ty b -∗
      ⎡ (b, 0) ◁ₗ{β} ty ⎤ ∗
      T (b, 0) β ty)
    ⊢ typed_lvalue ge f β (Evar _x c_ty) T.
  Proof.
    iIntros "(Hlvar & HT)" (Φ) "HΦ".
    iApply (wp_var_local _ _ _).
    iFrame.
    iIntros "Hlvar"; iDestruct ("HT" with "Hlvar") as "[own_l HT]".
    iApply ("HΦ" with "[$]"). done.
  Qed.

(*  Lemma type_call_syn T ef es:
    typed_val_expr (Call ef es) T :-
      vf, tyf ← {typed_val_expr ef};
      vl, tys ← iterate: es with [], [] {{e T vl tys,
                  v, ty ← {typed_val_expr e};
                  return T (vl ++ [v]) (tys ++ [ty])}};
      {typed_call vf (vf ◁ᵥ tyf) vl tys T}.
  Proof.
    iIntros "He". iIntros (Φ) "HΦ".
    iApply wp_call_bind. iApply "He". iIntros (vf tyf) "Hvf HT".
    iAssert ([∗ list] v;ty∈[];[], v ◁ᵥ ty)%I as "-#Htys". { done. }
    move: {2 3 5}[] => vl. move: {2 3}(@nil type) => tys.
    iInduction es as [|e es] "IH" forall (vl tys) => /=. 2: {
      iApply "HT". iIntros (v ty) "Hv Hnext". iApply ("IH" with "HΦ Hvf Hnext"). by iFrame.
    }
    by iApply ("HT" with "Hvf Htys").
  Qed.
  Lemma type_call : [type_from_syntax type_call_syn].
  Proof. exact type_call_syn. Qed.

  Lemma type_copy_alloc_id e1 e2 ot T:
    typed_val_expr e1 (λ v1 ty1, typed_val_expr e2 (λ v2 ty2, typed_copy_alloc_id v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2) ot T))
    ⊢ typed_val_expr (CopyAllocId ot e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 He2".
    wp_bind. iApply "He2". iIntros (v2 ty2) "Hv2 Hop".
    by iApply ("Hop" with "Hv1 Hv2").
  Qed.

  Lemma type_cas ot e1 e2 e3 T:
    typed_val_expr e1 (λ v1 ty1, typed_val_expr e2 (λ v2 ty2, typed_val_expr e3 (λ v3 ty3, typed_cas ot v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2) v3 (v3 ◁ᵥ ty3) T)))
    ⊢ typed_val_expr (CAS ot e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 He2".
    wp_bind. iApply "He2". iIntros (v2 ty2) "Hv2 He3".
    wp_bind. iApply "He3". iIntros (v3 ty3) "Hv3 Hop".
    by iApply ("Hop" with "Hv1 Hv2 Hv3").
  Qed.

  Lemma type_ife ot e1 e2 e3 T:
    typed_val_expr e1 (λ v ty, typed_if ot v (v ◁ᵥ ty) (typed_val_expr e2 T) (typed_val_expr e3 T))
    ⊢ typed_val_expr (IfE ot e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 Hif".
    iDestruct ("Hif" with "Hv1") as "HT". destruct ot => //.
    all: iDestruct "HT" as (zorl ?) "HT".
    - iApply wp_if_bool; [done|..]. by destruct zorl; iApply "HT".
    - iApply wp_if_int; [done|..]. by case_decide; iApply "HT".
    - case_bool_decide; iDestruct "HT" as "[Hpre HT]".
      + iApply (wp_if_ptr with "Hpre"); rewrite ?bool_decide_true //. by iApply "HT".
      + iApply (wp_if_ptr with "Hpre"); rewrite ?bool_decide_false //; try eauto. by iApply "HT".
  Qed.

  Lemma type_logical_and ot1 ot2 e1 e2 T:
    typed_val_expr e1 (λ v1 ty1, typed_if ot1 v1 (v1 ◁ᵥ ty1)
       (typed_val_expr e2 (λ v2 ty2, typed_if ot2 v2 (v2 ◁ᵥ ty2)
           (typed_value (i2v 1 i32) (T (i2v 1 i32))) (typed_value (i2v 0 i32) (T (i2v 0 i32)))))
       (typed_value (i2v 0 i32) (T (i2v 0 i32))))
    ⊢ typed_val_expr (e1 &&{ot1, ot2, i32} e2) T.
  Proof.
    iIntros "HT". rewrite /LogicalAnd. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (v ty) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    2: { by iApply type_val. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (v2 ty2) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT"; by iApply type_val.
  Qed.

  Lemma type_logical_or ot1 ot2 e1 e2 T:
    typed_val_expr e1 (λ v1 ty1, typed_if ot1 v1 (v1 ◁ᵥ ty1)
      (typed_value (i2v 1 i32) (T (i2v 1 i32)))
      (typed_val_expr e2 (λ v2 ty2, typed_if ot2 v2 (v2 ◁ᵥ ty2)
        (typed_value (i2v 1 i32) (T (i2v 1 i32))) (typed_value (i2v 0 i32) (T (i2v 0 i32))))))
    ⊢ typed_val_expr (e1 ||{ot1, ot2, i32} e2) T.
  Proof.
    iIntros "HT". rewrite /LogicalOr. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (v ty) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    1: { by iApply type_val. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (v2 ty2) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT"; by iApply type_val.
  Qed.

  Lemma type_skipe e T:
    typed_val_expr e (λ v ty, |={⊤}[∅]▷=> T v ty) ⊢ typed_val_expr (SkipE e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv HT".
    iApply (wp_step_fupd with "HT") => //.
    iApply wp_skip. iIntros "!> HT !>".
    by iApply ("HΦ" with "Hv HT").
  Qed.

  Lemma type_skipe' e T:
    typed_val_expr e T ⊢ typed_val_expr (SkipE e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv HT".
    iApply wp_skip. by iApply ("HΦ" with "Hv HT").
  Qed.

  Lemma type_annot_expr n {A} (a : A) e T:
    typed_val_expr e (λ v ty, typed_annot_expr n a v (v ◁ᵥ ty) (find_in_context (FindVal v) (λ ty, T v ty)))
    ⊢ typed_val_expr (AnnotExpr n a e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv HT". iDestruct ("HT" with "Hv") as "HT".
    iInduction n as [|n] "IH" forall (Φ). {
      rewrite /AnnotExpr/=.
      iApply fupd_wp.
      iMod "HT" as (?) "[HT ?] /=". iApply wp_value.
      iApply ("HΦ" with "[$] [$]").
    }
    rewrite annot_expr_S_r. wp_bind.
    iApply (wp_step_fupd with "HT") => //.
    iApply wp_skip. iIntros "!> HT !>".
    by iApply ("IH" with "HΦ HT").
  Qed.

  Lemma type_macro_expr m es T:
    typed_macro_expr m es T
    ⊢ typed_val_expr (MacroE m es) T.
  Proof. done. Qed.

  Lemma type_use ot T e o mc:
    ⌜if o is Na2Ord then False else True⌝ ∗ typed_read (if o is ScOrd then true else false) e ot mc T
    ⊢ typed_val_expr (use{ot, o, mc} e) T.
  Proof.
    iIntros "[% Hread]" (Φ) "HΦ".
    wp_bind. iApply "Hread".
    iIntros (l) "Hl". rewrite /Use.
    destruct o => //.
    1: iApply wp_atomic.
    2: iApply fupd_wp; iApply wp_fupd.
    all: iMod "Hl" as (v q ty Hly Hv) "(Hl&Hv&HT)"; iModIntro.
    all: iApply (wp_deref with "Hl") => //; try by eauto using val_to_of_loc.
    all: iIntros "!# %st Hl".
    all: iMod ("HT" with "Hl Hv") as (ty') "[Hv HT]"; iModIntro.
    all: by iApply ("HΦ" with "Hv HT").
  Qed.

  Lemma type_read T T' e ot (a : bool) mc:
    IntoPlaceCtx e T' →
    T' (λ K l, find_in_context (FindLoc l) (λ '(β1, ty1),
      typed_place K l β1 ty1 (λ l2 β2 ty2 typ R,
          typed_read_end a ⊤ l2 β2 ty2 ot mc (λ v ty2' ty3,
            l ◁ₗ{β1} typ ty2' -∗ R ty2' -∗ T v ty3))))
    ⊢ typed_read a e ot mc T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ) "HΦ".
    iApply (HT' with "HT'").
    iIntros (K l). iDestruct 1 as ([β ty]) "[Hl HP]".
    iApply ("HP" with "Hl").
    iIntros (l' β2 ty2 typ R) "Hl' Hc HT" => /=. iApply "HΦ".
    rewrite /typed_read_end. iMod ("HT" with "Hl'") as (q v ty3 Hly Hv) "(Hl&Hv&HT)".
    iModIntro. iExists _,_,_. iFrame "Hl Hv". iSplitR => //. iSplit => //.
    iIntros "!# %st Hl Hv".
    iMod ("HT" with "Hl Hv") as (ty' ty4) "(Hv&Hl&HT)".
    iMod ("Hc" with "Hl") as "[? ?]". iExists _. iFrame. by iApply ("HT" with "[$]").
  Qed.

  Lemma type_read_copy a β l ty ly E mc {HC: CopyAs l β ty} T:
    ((HC (λ ty', ⌜ty'.(ty_has_op_type) ly MCCopy⌝ ∗ ⌜mtE ⊆ E⌝ ∗ ∀ v, T v (ty' : type) ty')).(i2p_P))
    ⊢ typed_read_end a E l β ty ly mc T.
  Proof.
    rewrite /typed_read_end. iIntros "Hs Hl". iDestruct (i2p_proof with "Hs Hl") as (ty') "(Hl&%&%&%&HT)".
    destruct β.
    - iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hclose".
      iDestruct (ty_aligned with "Hl") as %?; [done|].
      iDestruct (ty_deref with "Hl") as (v) "[Hl #Hv]"; [done|].
      iDestruct (ty_size_eq with "Hv") as %?; [done|].
      iExists _, _, _. iFrame "∗Hv". do 2 iSplitR => //=.
      iIntros "!# %st Hl _". iMod "Hclose". iModIntro.
      iExists _, _. iDestruct (ty_ref with "[//] Hl Hv") as "$"; [done|]. iSplitR "HT" => //.
      destruct mc => //.
      by iApply (ty_memcast_compat_copy with "Hv").
    - iRevert "Hl". iIntros "#Hl".
      iMod (copy_shr_acc with "Hl") as (? q' v) "[Hmt [Hv Hc]]" => //.
      iDestruct (ty_size_eq with "Hv") as "#>%"; [done|].
      iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hclose".
      iExists _, _, _. iFrame. do 2 iSplit => //=.
      iIntros "!# %st Hmt Hv". iMod "Hclose". iModIntro.
      iExists _, _. iFrame "Hl". iSplitR "HT"; [|done].
      destruct mc => //.
      by iApply (ty_memcast_compat_copy with "Hv").
  Qed.
  Definition type_read_copy_inst := [instance type_read_copy].
  Global Existing Instance type_read_copy_inst | 10.
*)

  (* for expr `e:=v` => eval_expr e = l ∧ typed l v  *)
  (* typed_lvalue e (typed_write_end ...)   *)

  (* Ke: a simple version of type_write that treat typed_place as just typed_val_expr. 
         Not so sure about what's inside typed_val_expr outside of typed_write_end. *)
  Lemma type_write_simple ge f β1 (a : bool) ty T e v ot:
    (typed_lvalue ge f β1 e (λ l β2 ty1,
      typed_write_end a ⊤ ot v ty l β2 ty1 (λ ty3:type, ⎡l ◁ₗ{β1} ty3⎤ -∗ T)))%I
    ⊢ typed_write ge f a e ot v ty T.
  Proof.
    iIntros "typed_e".
    iIntros (Φ) "HΦ".
    unfold typed_lvalue.
    iApply "typed_e". iIntros (l ty1) "Hv typed_write_end".
    iApply "HΦ".
    iIntros "own_v".
    unfold typed_write_end.
    iMod ("typed_write_end" with "Hv own_v") as "($ & $ & H)". iModIntro. iModIntro.
    iIntros "l↦". iMod ("H" with "l↦") as (ty3) "[own_l T]".
    by iApply "T".
  Qed.

  Lemma type_write_own_copy a E ty l2 ty2 v ot (T:type->assert):
    typed_write_end a E ot v ty l2 Own ty2 T where
    `{!Copyable ty}
    `{!TCDone (ty2.(ty_has_op_type) ot MCNone)} :-
      exhale <affine> ⌜ty.(ty_has_op_type) ot MCNone⌝;
      inhale ⎡v ◁ᵥₐₗ|ot| ty⎤;
      inhale ∃ v', ⎡v' ◁ᵥ|ot| ty2⎤;
      return T ty.
  Proof.
    unfold typed_write_end, TCDone => ??. iDestruct 1 as (?) "HT".
    iIntros "Hl #Hv".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v') "[Hl Hv']"; [done|].
    iDestruct (ty_size_eq with "Hv'") as %?; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hmask".
    iSplit; [done|]. iSplitL "Hl". 
    { rewrite mapsto_layout_iff_mapsto_and_layout. iExists _. iSplit;done. }
    iIntros "!# Hl". iMod "Hmask". iModIntro.
    iExists _.
    iPoseProof (ty_ref with "[] Hl Hv") as "$"; try done.
    rewrite /ty_own_val_at.
    iDestruct ("HT" with "Hv [Hv']") as "HT"; try done.
    iExists _; done.
  Qed.
  Definition type_write_own_copy_inst := [instance type_write_own_copy].
  Global Existing Instance type_write_own_copy_inst | 20.
  (*

  (* Note that there is also [type_write_own] in singleton.v which applies if one can prove MCId. *)
  Lemma type_write_own_move a E ty l2 ty2 v ot T:
    typed_write_end a E ot v ty l2 Own ty2 T where
    `{!TCDone (ty2.(ty_has_op_type) (UntypedOp (ot_layout ot)) MCNone)} :-
      exhale ⌜ty.(ty_has_op_type) (UntypedOp (ot_layout ot)) MCNone⌝;
      ∀ v', inhale v' ◁ᵥ ty2; return T ty.
  Proof.
    unfold TCDone, typed_write_end => ?. iDestruct 1 as (?) "HT". iIntros "Hl Hv".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v') "[Hl Hv']"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iDestruct (ty_size_eq with "Hv'") as %?; [done|].
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hmask".
    iSplit; [done|]. iSplitL "Hl". { iExists _. by iFrame. }
    iIntros "!# Hl". iMod "Hmask". iModIntro.
    iDestruct (ty_ref with "[] Hl Hv") as "?"; [done..|].
    iExists _. iFrame. by iApply "HT".
  Qed.
  Definition type_write_own_move_inst := [instance type_write_own_move].
  Global Existing Instance type_write_own_move_inst | 70.

  Lemma type_addr_of_place T T' e:
    IntoPlaceCtx e T' →
    T' (λ K l, find_in_context (FindLoc l) (λ '(β1, ty1),
      typed_place K l β1 ty1 (λ l2 β2 ty2 typ R,
                              typed_addr_of_end l2 β2 ty2 (λ β3 ty3 ty',
                  l ◁ₗ{β1} typ ty' -∗ R ty' -∗ T l2 β3 ty3))))
    ⊢ typed_addr_of e T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ) "HΦ".
    iApply @wp_fupd. iApply (HT' with "HT'").
    iIntros (K l). iDestruct 1 as ([β ty]) "[Hl HP]".
    iApply ("HP" with "Hl"). iIntros (l2 β2 ty2 typ R) "Hl' Hc HT".
    iMod ("HT" with "Hl'") as (β3 ty3 ty') "[Hty3 [Hty' HT]]".
    iMod ("Hc" with "Hty'") as "[Hc ?]". iModIntro.
    iApply ("HΦ" with "Hty3").
    by iApply ("HT" with "[$]").
  Qed.
*)
(*
  Lemma type_place_id l ty β T:
    T l β ty id (λ _, True)
    ⊢ typed_place l β ty T.
  Proof.
    unfold typed_place.
    iIntros  "HT Hl" (l2 β2 ty2 typ R) "Hl2". iApply ("HΦ" with "Hl [] HT").  by iIntros (ty') "$".
  Qed.s
  Definition type_place_id_inst := [instance type_place_id].
  Global Existing Instance type_place_id_inst | 20.

  Lemma copy_as_id l β ty `{!Copyable ty} T:
    T ty ⊢ copy_as l β ty T.
  Proof. iIntros "HT Hl". iExists _. by iFrame. Qed.
  Definition copy_as_id_inst := [instance copy_as_id].
  Global Existing Instance copy_as_id_inst | 1000.

  Lemma copy_as_refinement A l β (ty : rtype A) {HC: ∀ x, CopyAs l β (x @ ty)} T:
    (∀ x, (HC x T).(i2p_P)) ⊢ copy_as l β ty T.
  Proof.
    iIntros "HT Hl". unfold ty_of_rty; simpl_type. iDestruct "Hl" as (x) "Hl".
    iSpecialize ("HT" $! x). iDestruct (i2p_proof with "HT") as "HT". by iApply "HT".
  Qed.
  Definition copy_as_refinement_inst := [instance copy_as_refinement].
  Global Existing Instance copy_as_refinement_inst.

  Lemma annot_share l ty T:
    (l ◁ₗ{Shr} ty -∗ T)
    ⊢ typed_annot_stmt (ShareAnnot) l (l ◁ₗ ty) T.
  Proof.
    iIntros "HT Hl". iMod (ty_share with "Hl") => //.
    iApply step_fupd_intro => //. iModIntro. by iApply "HT".
  Qed.
  Definition annot_share_inst := [instance annot_share].
  Global Existing Instance annot_share_inst.

  Definition STOPPED : iProp Σ := False.
  Lemma annot_stop l β ty T:
    (l ◁ₗ{β} ty -∗ STOPPED)
    ⊢ typed_annot_stmt (StopAnnot) l (l ◁ₗ{β} ty) T.
  Proof. iIntros "HT Hl". iDestruct ("HT" with "Hl") as %[]. Qed.
  Definition annot_stop_inst := [instance annot_stop].
  Global Existing Instance annot_stop_inst.

  Lemma annot_unfold_once l β ty n {SH : SimplifyHyp (l ◁ₗ{β} ty) (Some (Npos n))} T:
    (SH T).(i2p_P)
    ⊢ typed_annot_stmt UnfoldOnceAnnot l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as "HT" => /=.
    by iApply step_fupd_intro.
  Qed.
  Definition annot_unfold_once_inst := [instance annot_unfold_once].
  Global Existing Instance annot_unfold_once_inst.

  Lemma annot_learn l β ty {L : Learnable (l ◁ₗ{β} ty)} T:
    (learnable_data L ∗ l ◁ₗ{β} ty -∗ T)
    ⊢ typed_annot_stmt (LearnAnnot) l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "HT Hl". iApply step_fupd_intro => //.
    iDestruct (learnable_learn with "Hl") as "#H".
    iApply "HT". by iFrame.
  Qed.
  Definition annot_learn_inst := [instance annot_learn].
  Global Existing Instance annot_learn_inst.

(*  Lemma annot_learn_aligment l β ty n `{!LearnAlignment β ty (Some n)} T:
    (⌜l `aligned_to` n⌝ -∗ l ◁ₗ{β} ty -∗ T)
    ⊢ typed_annot_stmt (LearnAlignmentAnnot) l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "HT Hl". iApply step_fupd_intro => //. iModIntro.
    iDestruct (learnalign_learn with "Hl") as %?.
    by iApply "HT".
  Qed.
  Definition annot_learn_aligment_inst := [instance annot_learn_aligment].
  Global Existing Instance annot_learn_aligment_inst.*)
End typing.

(* This must be an Hint Extern because an instance would be a big slowdown . *)
Global Hint Extern 50 (Subsume (_ ◁ₗ{_} ?ty _) (λ _, _ ◁ₗ{_} ?ty2 _)%I) =>
  match ty with | ty2 => is_var ty; class_apply subtype_var_inst end : typeclass_instances.

Global Hint Extern 5 (Subsume (_ ◁ₗ{_} _) (λ _, _ ◁ₗ{_.1ₗ} _)%I) =>
  (class_apply subsume_place_own_ex_inst) : typeclass_instances.

Global Hint Extern 5 (Subsume (_ ◁ₗ{_} _) (λ _, _ ◁ₗ{_} _.1ₗ)%I) =>
  (class_apply subsume_place_ty_ex_inst) : typeclass_instances.


(*Global Typeclasses Opaque typed_block.
*)
*)

  Lemma type_seq Espec ge f s1 s2 T:
    typed_stmt Espec ge s1 f (λ v ty, match v with None => typed_stmt Espec ge s2 f T
                                       | _ => T v ty end)
    ⊢ typed_stmt Espec ge (Ssequence s1 s2) f T.
  Proof.
    iIntros "H". unfold typed_stmt.
    rewrite -wp_seq /=.
    iApply (wp_conseq with "H"); auto.
  Qed.

End typing.
