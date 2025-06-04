From iris.bi Require Export monpred.
Require Import VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import iris_ora.algebra.gmap_view.
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Export compcert.common.AST.
Require Export compcert.cfrontend.Ctypes.

Require Import VST.veric.composite_compute.
Require Import VST.veric.align_mem.
Require Import VST.veric.val_lemmas.

Require Export VST.veric.compspecs.

Open Scope Z_scope.

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then None else if Int.eq n Int.zero then Some false else None
   | Vlong n, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then if Int64.eq n Int64.zero then Some false else None else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) => Some true
   | Vfloat f, Tfloat F64 _ => Some (negb(Float.cmp Ceq f Float.zero))
   | Vsingle f, Tfloat F32 _ => Some (negb(Float32.cmp Ceq f Float32.zero))
   | _, _ => None
   end.

Definition type_is_by_value (t:type) : bool :=
  match t with
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tpointer _ _ => true
  | _ => false
  end.

Definition type_is_by_reference t : bool :=
  match t with
  | Tarray _ _ _
  | Tfunction _ _ _ => true
  | _ => false
  end.

(** GENERAL KV-Maps **)
(* deprecate? *)

Set Implicit Arguments.

Module Map. Section map.
Context (B : Type).

Definition t := positive -> option B.

Definition get (h: t) (a:positive) : option B := h a.

Definition set (a:positive) (v: B) (h: t) : t :=
  fun i => if ident_eq i a then Some v else h i.

Definition remove (a: positive) (h: t) : t :=
  fun i => if ident_eq i a then None else h i.

Definition empty : t := fun _ => None.

(** MAP Axioms **)

Lemma gss h x v : get (set x v h) x = Some v.
unfold get, set; if_tac; intuition.
Qed.

Lemma gso h x y v : x<>y -> get (set x v h) y = get h y.
unfold get, set; intros; if_tac; intuition congruence.
Qed.

Lemma grs h x : get (remove x h) x = None.
unfold get, remove; intros; if_tac; intuition.
Qed.

Lemma gro h x y : x<>y -> get (remove x h) y = get h y.
unfold get, remove; intros; if_tac; intuition congruence.
Qed.

Lemma ext h h' : (forall x, get h x = get h' x) -> h=h'.
Proof.
intros. extensionality x. apply H.
Qed.

Lemma override (a: positive) (b b' : B) h : set a b' (set a b h) = set a b' h.
Proof.
apply ext; intros; unfold get, set; if_tac; intuition. Qed.

Lemma gsspec:
    forall (i j: positive) (x: B) (m: t),
    get (set j x m) i = if ident_eq i j then Some x else get m i.
Proof.
intros. unfold get; unfold set; if_tac; intuition.
Qed.

Lemma override_same : forall id t (x:B), get t id = Some x -> set id x t = t.
Proof.
intros. unfold set. unfold get in H.  apply ext. intros. unfold get.
if_tac; subst; auto.
Qed.

End map.

End Map.

Unset Implicit Arguments.

Global Instance EqDec_calling_convention: EqDec calling_convention.
Proof.
  hnf. decide equality.
  destruct cc_structret, cc_structret0; subst; try tauto; right; congruence.
  destruct cc_unproto, cc_unproto0;  subst; try tauto; right; congruence.
  destruct cc_vararg, cc_vararg0; subst; try tauto.
  destruct (zeq z0 z); subst; [left|right]; congruence.
  right; congruence.
  right; congruence.
Qed.

(** Environment Definitions **)
Section FUNSPEC.

Definition genviron := gmap ident block.

Definition venviron := gmap ident (block * type).

Definition tenviron := gmap ident val.

Definition environ : Type := (genviron * venviron * tenviron).

Definition ge_of (rho: environ) : genviron :=
  match rho with (ge, ve, te) => ge end.

Definition ve_of (rho: environ) : venviron :=
  match rho with (ge, ve, te) => ve end.

Definition te_of (rho: environ) : tenviron :=
  match rho with (ge, ve, te) => te end.

Definition mkEnviron a b c : environ := (a, b, c).

Definition any_environ : environ := (empty, empty, empty).

Definition argsEnviron:Type := genviron * (list val).

Global Instance EqDec_type: EqDec type := type_eq.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Definition typesig := (list type * type)%type. (*funsig without the identifiers*)

Definition typesig_of_funsig (f:funsig):typesig := (map snd (fst f), snd f).

Context {Σ : gFunctors}.

(*Potential alternative that does not use Ctypes
Inductive funspec :=
   mk_funspec: AST.signature -> forall (A: TypeTree)
     (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: super_non_expansive P) (Q_ne: super_non_expansive Q),
    funspec.
 *)

(* TODO: This isn't part of the core logic; move it to VeriC eventually. *)
Section funspec.

(* funspecs are effectively dependent pairs of an algebra and a pair of assertions on that algebra.
   This means we have to take some care to define them in a way that avoids universe inconsistencies. *)

(* Reify the type of the funspec's WITH clause. *)
Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | CompspecsType: TypeTree
  | Mpred: TypeTree
(*  | DependentType: nat -> TypeTree *)
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | DiscreteFunType: Type -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
(*  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree*)
  | ListType: TypeTree -> TypeTree.

Fixpoint dependent_type_functor_rec (T : TypeTree) : oFunctor :=
  match T with
  | ConstType t => constOF (leibnizO t)
  | CompspecsType => constOF (leibnizO compspecs)
  | Mpred => idOF
  | ProdType a b => dependent_type_functor_rec a * dependent_type_functor_rec b
  | DiscreteFunType a b => a -d> dependent_type_functor_rec b
  | ArrowType a b => dependent_type_functor_rec a -n> dependent_type_functor_rec b
  | SigType _ f => sigTOF (fun i => dependent_type_functor_rec (f i))
  | ListType t => listOF (dependent_type_functor_rec t)
  end.

(* Current theory: funspecs can only mention args/retval and should otherwise
   not say anything about the environment. *)
Definition ArgsTT A := ArrowType A (DiscreteFunType (genviron * list val) ((*DiscreteFunType nat*) Mpred)).
Definition AssertTT A := ArrowType A (DiscreteFunType (option val) ((*DiscreteFunType nat*) Mpred)).
Definition MaskTT A := ArrowType A (ConstType coPset).

Section ofe.

Context `{Cofe PROP1} `{Cofe PROP2}.

Inductive funspec_ :=
   mk_funspec (sig : typesig) (cc : calling_convention) (A: TypeTree)
     (E: oFunctor_car (dependent_type_functor_rec (MaskTT A)) PROP1 PROP2)
     (P: oFunctor_car (dependent_type_functor_rec (ArgsTT A)) PROP1 PROP2)
     (Q: oFunctor_car (dependent_type_functor_rec (AssertTT A)) PROP1 PROP2).

Import EqNotations.

Lemma E_eq : forall {A1 A2}, A1 = A2 ->
  oFunctor_car (dependent_type_functor_rec (MaskTT A1)) PROP1 PROP2 = oFunctor_car (dependent_type_functor_rec (MaskTT A2)) PROP1 PROP2.
Proof.
  by intros ?? ->.
Defined.

Lemma pre_eq : forall {A1 A2}, A1 = A2 ->
  oFunctor_car (dependent_type_functor_rec (ArgsTT A1)) PROP1 PROP2 = oFunctor_car (dependent_type_functor_rec (ArgsTT A2)) PROP1 PROP2.
Proof.
  by intros ?? ->.
Defined.

Lemma post_eq : forall {A1 A2}, A1 = A2 ->
  oFunctor_car (dependent_type_functor_rec (AssertTT A1)) PROP1 PROP2 = oFunctor_car (dependent_type_functor_rec (AssertTT A2)) PROP1 PROP2.
Proof.
  by intros ?? ->.
Defined.

Local Instance funspec_dist : Dist funspec_ := λ n f1 f2,
  match f1, f2 with
  | mk_funspec sig1 cc1 A1 E1 P1 Q1, mk_funspec sig2 cc2 A2 E2 P2 Q2 =>
      sig1 = sig2 /\ cc1 = cc2 /\ ∃ H : A1 = A2, rew (E_eq H) in E1 ≡{n}≡ E2 /\ rew (pre_eq H) in P1 ≡{n}≡ P2 /\ rew (post_eq H) in Q1 ≡{n}≡ Q2
  end.

Local Instance funspec_equiv : Equiv funspec_ := λ f1 f2, forall n, f1 ≡{n}≡ f2.

Global Instance mk_funspec_proper sig cc A : Proper (equiv ==> equiv ==> equiv ==> equiv) (mk_funspec sig cc A).
Proof.
  repeat (split; first done).
  exists eq_refl; eauto.
Qed.

Global Instance mk_funspec_ne sig cc A : NonExpansive3 (mk_funspec sig cc A).
Proof.
  intros ??????????.
  repeat (split; first done).
  by exists eq_refl.
Qed.

Lemma funspec_ofe_mixin : OfeMixin funspec_.
Proof.
  split; try done.
  - split.
    + intros []; repeat (split; auto).
      exists eq_refl; done.
    + intros [] [] (-> & -> & -> & ? & ? & ?). repeat (split; auto).
      exists eq_refl; done.
    + intros [] [] [] (-> & -> & -> & ? & ? & ?) (-> & -> & -> & ? & ? & ?); repeat (split; auto).
      exists eq_refl; split3; etrans; eauto.
  - intros ?? [] [] (-> & -> & -> & ? & ? & ?) ?; repeat (split; auto).
    exists eq_refl; split3; eapply dist_lt; eauto.
Qed.
Canonical Structure funspecO := Ofe funspec_ funspec_ofe_mixin.

End ofe.
Global Arguments funspec_ _ {_} _ {_}.
Global Arguments funspecO _ {_} _ {_}.

Section ofunctor.

Program Definition funspecOF (PF : oFunctor) `{forall (A : ofe) (HA : Cofe A) (B : ofe) (HB : Cofe B), Cofe (oFunctor_car PF A B)} : oFunctor := {|
    oFunctor_car A CA B CB := funspecO (oFunctor_car PF B A) (oFunctor_car PF A B);
    oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := λne f, match f with mk_funspec sig cc A E P Q =>
      mk_funspec sig cc A (oFunctor_map (oFunctor_oFunctor_compose (dependent_type_functor_rec (MaskTT A)) PF) fg E)
                          (oFunctor_map (oFunctor_oFunctor_compose (dependent_type_functor_rec (ArgsTT A)) PF) fg P)
                          (oFunctor_map (oFunctor_oFunctor_compose (dependent_type_functor_rec (AssertTT A)) PF) fg Q) end
  |}.
Next Obligation.
Proof.
  intros. intros [] [].
  intros (<- & <- & <- & ? & HP & HQ); repeat split; auto.
  exists eq_refl; split3; by apply ofe_mor_map_ne.
Qed.
Next Obligation.
Proof.
  intros. intros fg fg' Hfg [].
  repeat split; auto.
  exists eq_refl; split3; rewrite /eq_rect /E_eq /pre_eq /post_eq /eq_ind_r /eq_ind /eq_sym; (apply ofe_mor_car_ne; [f_equiv|]; done).
Qed.
Next Obligation.
  intros. destruct x.
  repeat split; auto.
  exists eq_refl; split3; apply equiv_dist; rewrite /eq_rect /E_eq /pre_eq /post_eq /eq_ind_r /eq_ind /eq_sym oFunctor_map_id //.
Qed.
Next Obligation.
  intros. destruct x.
  repeat split; auto.
  exists eq_refl; split3; apply equiv_dist; rewrite /eq_rect /E_eq /pre_eq /post_eq /eq_ind_r /eq_ind /eq_sym oFunctor_map_compose //.
Qed.

Global Instance funspecOF_contractive {PF} `{forall (A : ofe) (HA : Cofe A) (B : ofe) (HB : Cofe B), Cofe (oFunctor_car PF A B)} :
    oFunctorContractive PF → oFunctorContractive (funspecOF PF).
Proof.
  rewrite /oFunctorContractive; intros.
  intros ??? []; repeat split; auto.
  exists eq_refl; split3; rewrite /eq_rect /E_eq /pre_eq /post_eq /eq_ind_r /eq_ind /eq_sym;
    (apply @ofe_mor_car_ne; [|done]; apply @oFunctor_map_contractive; [apply oFunctor_oFunctor_compose_contractive_2|]; done).
Qed.

End ofunctor.

End funspec.

(*Program Fixpoint dtfr_later {PROP1} `{Cofe PROP1} {PROP2} `{Cofe PROP2} A : oFunctor_car (dependent_type_functor_rec A) PROP1 PROP2 -> oFunctor_car (dependent_type_functor_rec A) (laterO PROP1) (laterO PROP2) :=
  match A with
  | ConstType t => id
  | CompspecsType => id
  | Mpred => Next
  | ProdType a b => λ x, (dtfr_later a (fst x), dtfr_later b (snd x))
  | DiscreteFunType a b => λ x y, dtfr_later b (x y)
  | ArrowType a b => λ x, (*λne y, dtfr_later b (x (dtfr_unlater a y))*) laterO_map x
  | SigType _ f => λ x, match x with existT y P => existT y (dtfr_later (f y) P) end
  | ListType t => map (dtfr_later t)
  end
with dtfr_unlater {PROP1} `{Cofe PROP1} {PROP2} `{Cofe PROP2} A : oFunctor_car (dependent_type_functor_rec A) (laterO PROP1) (laterO PROP2) -> oFunctor_car (dependent_type_functor_rec A) PROP1 PROP2 :=
  match A with
  | ConstType t => id
  | CompspecsType => id
  | Mpred => later_car
  | ProdType a b => λ x, (dtfr_unlater a (fst x), dtfr_unlater b (snd x))
  | DiscreteFunType a b => λ x y, dtfr_unlater b (x y)
  | ArrowType a b => λ x, λne y, dtfr_unlater b (x (dtfr_later a y))
  | SigType _ f => λ x, match x with existT y P => existT y (dtfr_unlater (f y) P) end
  | ListType t => map (dtfr_unlater t)
  end.
Next Obligation.
Proof.
  intros.
  intros ???.
  simpl in x.
  subst.
  induction a; simpl.
Locate "-n>".*)

(*Program Definition dtfr_later {PROP1} `{Cofe PROP1} {PROP2} `{Cofe PROP2} A : oFunctor_car (dependent_type_functor_rec A) PROP1 PROP2 -> oFunctor_car (dependent_type_functor_rec A) (laterO PROP1) (laterO PROP2) :=
  λ x, oFunctor_map (dependent_type_functor_rec A) (λne x, Next x, λne x, Next x) x.
Next Obligation.
Proof.
  intros.*)

Definition funspecO' := (laterO (funspecO (iPropO Σ) (iPropO Σ))).
Definition funspecOF' := (laterOF (funspecOF idOF)).
Definition dtfr A := (oFunctor_car (dependent_type_functor_rec A) (iProp Σ) (iProp Σ)).

Lemma OfeMor_eq : forall {A B : ofe} (f1 f2 : A -> B) {H1 H2}, f1 = f2 -> @OfeMor A B f1 H1 = @OfeMor A B f2 H2.
Proof.
  intros; subst.
  f_equal. apply proof_irr.
Qed.

Lemma funspec_equivI PROP1 `{Cofe PROP1} PROP2 `{Cofe PROP2} (f1 f2 : funspec_ PROP1 PROP2) : (f1 ≡ f2 : iProp Σ) ⊣⊢ ∃ sig cc A E P1 P2 Q1 Q2,
  ⌜f1 = mk_funspec sig cc A E P1 Q1 ∧ f2 = mk_funspec sig cc A E P2 Q2⌝ ∧ P1 ≡ P2 ∧ Q1 ≡ Q2.
Proof.
  ouPred.unseal; split=> n x ?.
  destruct f1, f2; split.
  - intros (<- & <- & <- & HE & HP & HQ); simpl in *.
    exists sig, cc, A, E, P, P0, Q, Q0; repeat split; try done.
    f_equal. destruct E, E0. apply OfeMor_eq; extensionality y.
    symmetry; apply HE.
  - intros (? & ? & ? & ? & ? & ? & ? & ? & ([=] & [=]) & ? & ?); subst.
    repeat match goal with H : existT _ _ = existT _ _ |- _ => apply inj_pair2 in H end; subst.
    split3; auto; exists eq_refl; done.
Qed.

End FUNSPEC.

(* collect up all the ghost state required for the logic
   Should this include external state as well? *)
Class funspecGS Σ := FunspecG {
    funspec_inG :: inG Σ (gmap_viewR address (@funspecO' Σ));
    funspec_name : gname
}.

Class heapGS Σ := HeapGS {
  heapGS_invGS :: invGS_gen HasNoLc Σ;
  heapGS_gen_heapGS :: gen_heapGS share address resource Σ;
  heapGS_funspecGS :: funspecGS Σ (* can actually do without this in the core logic *)
}.

(* Because Clight uses environment semantics, it's natural for us to treat
   the environment as part of the state and use separation logic on it (e.g., use
   ∗ to ensure that unrelated assertions aren't affected by an assignment).
   But from this perspective, entering a new stackframe is a non-frame-preserving
   operation. We address this by treating the entire stack of variable names as a
   resource, so that entering a new frame is simply moving up the stack rather
   than clearing existing resources. *)

Notation fixed_fracR A := (prodR (iris.algebra.agree.agreeR (leibnizO frac))
  (prodR fracR A)).

Notation frameR := (prodR ((iris.algebra.gmap.gmapR ident (iris.algebra.excl.exclR (leibnizO (block * type)))))
  ((iris.algebra.gmap.gmapR ident (iris.algebra.excl.exclR (leibnizO val))))).

Notation envR := (ora.prodR
    (ext_order.inclR (gmap_view.gmap_viewR ident (agree.agreeR (leibnizO block))))
    (ext_order.inclR (iris.algebra.auth.authR (iris.algebra.gmap.gmapUR nat (fixed_fracR frameR))))).

(*Definition envUR := Uora' envR (ofe_mixin envR) (cmra_mixin envR) (ora_mixin envR) (ucmra_mixin envR).*)

Class envGS Σ := EnvGS {
  envGS_inG :: inG Σ envR;
  env_name : gname
}.

Definition mpred `{heapGS Σ} := iProp Σ.

(* assertions are monPreds on stack level *)
Definition stack_index : biIndex := {| bi_index_type := nat; bi_index_rel := eq |}.

Definition assert `{!envGS Σ} := monPred stack_index (iPropI Σ).

Program Definition assert_of `{!envGS Σ} (P : nat -> iProp Σ) : assert := {| monPred_at := P |}.

Section heap.

Context `{!heapGS Σ} `{!envGS Σ}.

(* funspecs on mpreds *)
Definition funspec := funspec_ mpred mpred.
Definition NDmk_funspec (sig : typesig) (cc : calling_convention) A (P : A -> (genviron * list val) -> mpred) (Q : A -> option val -> mpred) : funspec :=
  mk_funspec sig cc (ConstType A) (λne a, ⊤) (λne (a : leibnizO A), (P a) : _ -d> mpred) (λne (a : leibnizO A), (Q a) : _ -d> mpred).

Definition funspec_unfold (f : funspec) : laterO funspec := Next f.

Definition varspecs : Type := list (ident * type).

Definition funspecs := list (ident * funspec_ (iProp Σ) (iProp Σ)).


Definition type_of_funspec (fs: funspec) : type :=
  match fs with mk_funspec fsig cc _ _ _ _ => 
     Tfunction (fst fsig) (snd fsig) cc end.

Fixpoint make_tycontext_s (G: funspecs) :=
 match G with
 | nil => Maps.PTree.empty funspec
 | (id,f)::r => Maps.PTree.set id f (make_tycontext_s r)
 end.

Lemma entails_refl : forall (P : mpred), P ⊢ P.
Proof. done. Qed.

Lemma pure_intro_l : forall (P : Prop) (Q R : mpred), P -> (Q ⊢ R) -> Q ⊢ ⌜P⌝ ∧ R.
Proof.
  intros ???? ->; iIntros "$"; auto.
Qed.

Lemma pure_intro_r : forall (P : Prop) (Q R : mpred), P -> (Q ⊢ R) -> Q ⊢ R ∧ ⌜P⌝.
Proof.
  intros ???? ->; iIntros "$"; auto.
Qed.

End heap.

Definition int_range (sz: intsize) (sgn: signedness) (i: int) :=
 match sz, sgn with
 | I8, Signed => -128 <= Int.signed i < 128
 | I8, Unsigned => 0 <= Int.unsigned i < 256
 | I16, Signed => -32768 <= Int.signed i < 32768
 | I16, Unsigned => 0 <= Int.unsigned i < 65536
 | I32, Signed => -2147483648 <= Int.signed i < 2147483648
 | I32, Unsigned => 0 <= Int.unsigned i < 4294967296
 | IBool, _ => 0 <= Int.unsigned i < 256
 end.

Lemma size_chunk_sizeof: forall env t ch, access_mode t = By_value ch -> sizeof env t = Memdata.size_chunk ch.
Proof.
  intros.
  destruct t; inversion H.
  - destruct i, s; inversion H1; reflexivity.
  - destruct s; inversion H1; reflexivity.
  - destruct f; inversion H1; reflexivity.
  - inversion H1; reflexivity.
Qed.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Arguments sizeof_pos {env} t _.
Arguments alignof_pos {env} t.

Arguments complete_legal_cosu_type {cenv} !t / .

(* TODO: handle other part of compspecs like this. *)
Goal forall {cs: compspecs} t, sizeof t >= 0.
Proof. intros. apply sizeof_pos.
Abort.

Definition idset := Maps.PTree.t unit.

Definition idset0 : idset := Maps.PTree.empty _.
Definition idset1 (id: ident) : idset := Maps.PTree.set id tt idset0.
Definition insert_idset (id: ident) (S: idset) : idset :=
  Maps.PTree.set id tt S.

Definition eval_id (id: ident) (rho: environ) := force_val (lookup id (te_of rho)).

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  (ge_of rho, ve_of rho, <[x := v]>(te_of rho)).

Lemma eval_id_same: forall rho id v, eval_id id (env_set rho id v) = v.
Proof. unfold eval_id; intros; simpl. unfold force_val. rewrite lookup_insert. auto.
Qed.

Lemma eval_id_other: forall rho id id' v,
   id<>id' -> eval_id id' (env_set rho id v) = eval_id id' rho.
Proof.
 unfold eval_id, force_val; intros. simpl. rewrite lookup_insert_ne; auto.
Qed.

#[export] Hint Rewrite eval_id_same : normalize norm.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : normalize norm.

(* TWO ALTERNATE WAYS OF DOING LIFTING *)
(* LIFTING METHOD ONE: *)
Definition lift0 {B} (P: B) : environ -> B := fun _ => P.
Definition lift1 {A1 B} (P: A1 -> B) (f1: environ -> A1) : environ -> B := fun rho => P (f1 rho).
Definition lift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: environ -> A1) (f2: environ -> A2):
   environ -> B := fun rho => P (f1 rho) (f2 rho).
Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B)
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3) :  environ -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Definition lift4 {A1 A2 A3 A4 B} (P: A1 -> A2 -> A3 -> A4 -> B)
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3)(f4: environ -> A4):  environ -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho) (f4 rho).

Definition alift0 {B} (P: B) : argsEnviron -> B := fun _ => P.
Definition alift1 {A1 B} (P: A1 -> B) (f1: argsEnviron -> A1) : argsEnviron -> B := fun rho => P (f1 rho).
Definition alift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: argsEnviron -> A1) (f2: argsEnviron -> A2):
   argsEnviron -> B := fun rho => P (f1 rho) (f2 rho).
Definition alift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B)
     (f1: argsEnviron -> A1) (f2: argsEnviron -> A2) (f3: argsEnviron -> A3) :  argsEnviron -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Definition alift4 {A1 A2 A3 A4 B} (P: A1 -> A2 -> A3 -> A4 -> B)
     (f1: argsEnviron -> A1) (f2: argsEnviron -> A2) (f3: argsEnviron -> A3)(f4: argsEnviron -> A4):  argsEnviron -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho) (f4 rho).

(* LIFTING METHOD TWO: *)
Require Import VST.veric.lift.
Set Warnings "-projection-no-head-constant,-redundant-canonical-projection".
Canonical Structure LiftEnviron := Tend environ.
Set Warnings "projection-no-head-constant,redundant-canonical-projection".

Set Warnings "-projection-no-head-constant,-redundant-canonical-projection".
Canonical Structure LiftAEnviron := Tend argsEnviron.
Set Warnings "projection-no-head-constant,redundant-canonical-projection".

Ltac super_unfold_lift :=
  cbv delta [liftx LiftEnviron LiftAEnviron Tarrow Tend lift_S lift_T lift_prod
  lift_last lifted lift_uncurry_open lift_curry lift lift0 lift1 lift2 lift3 alift0 alift1 alift2 alift3] beta iota in *.

Ltac raise_rho' :=
  repeat (rewrite monPred_at_and ||
          rewrite monPred_at_sep ||
          rewrite monPred_at_or ||
          rewrite monPred_at_emp ||
          rewrite monPred_at_pure ||
          rewrite monPred_at_later ||
          rewrite monPred_at_persistently ||
          rewrite monPred_at_wand ||
          rewrite monPred_at_embed ||
          rewrite monPred_at_except_0 ||
          rewrite monPred_at_intuitionistically ||
          rewrite monPred_at_absorbingly ||
          rewrite monPred_at_affinely ||
          rewrite monPred_at_in ||
          rewrite monPred_at_subjectively ||
          rewrite monPred_at_objectively ||
          rewrite monPred_at_persistently_if ||
          rewrite monPred_at_laterN ||
          rewrite monPred_at_absorbingly_if ||
          rewrite monPred_at_intuitionistically_if ||
          rewrite monPred_at_affinely_if ||
          rewrite monPred_at_exist ||
          rewrite monPred_at_forall ||
          rewrite monPred_at_bupd ||
          rewrite monPred_at_internal_eq ||
          rewrite monPred_at_plainly ||
          rewrite monPred_at_fupd ||
          rewrite monPred_at_impl ||
          rewrite monPred_at_wand ||
          rewrite monPred_at_big_sepL ||
          rewrite monPred_at_big_sepS ||
          rewrite monPred_at_big_sepMS ||
          rewrite monPred_at_big_sepM ||
          simpl).

(* switch from an entailment on asserts to mpreds; mostly the same as monPred.unseal *)
Ltac raise_rho :=
  try (constructor; intro rho); 
  raise_rho'.
