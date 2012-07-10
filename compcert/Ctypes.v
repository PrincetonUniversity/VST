Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.

(** ** Types *)

(** Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and 
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16, or 32 bits, or the special [IBool] size
  standing for the C99 [_Bool] type. *)

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.

(** Float types come in two sizes: 32 bits (single precision)
  and 64-bit (double precision). *)

Inductive floatsize : Type :=
  | F32: floatsize
  | F64: floatsize.

(** Every type carries a set of attributes.  Currently, only one
  attribute is modeled: [volatile]. *)

Record attr : Type := mk_attr {
  attr_volatile: bool
}.

Definition noattr := {| attr_volatile := false |}.

(** The syntax of type expressions.  Some points to note:
- Array types [Tarray n] carry the size [n] of the array.
  Arrays with unknown sizes are represented by pointer types.
- Function types [Tfunction targs tres] specify the number and types
  of the function arguments (list [targs]), and the type of the
  function result ([tres]).  Variadic functions and old-style unprototyped
  functions are not supported.
- In C, struct and union types are named and compared by name.
  This enables the definition of recursive struct types such as
<<
  struct s1 { int n; struct * s1 next; };
>>
  Note that recursion within types must go through a pointer type.
  For instance, the following is not allowed in C.
<<
  struct s2 { int n; struct s2 next; };
>>
  In Compcert C, struct and union types [Tstruct id fields] and
  [Tunion id fields] are compared by structure: the [fields]
  argument gives the names and types of the members.  The identifier
  [id] is a local name which can be used in conjuction with the
  [Tcomp_ptr] constructor to express recursive types.  [Tcomp_ptr id]
  stands for a pointer type to the nearest enclosing [Tstruct]
  or [Tunion] type named [id].  For instance. the structure [s1]
  defined above in C is expressed by
<<
  Tstruct "s1" (Fcons "n" (Tint I32 Signed)
               (Fcons "next" (Tcomp_ptr "s1")
               Fnil))
>>
  Note that the incorrect structure [s2] above cannot be expressed at
  all, since [Tcomp_ptr] lets us refer to a pointer to an enclosing
  structure or union, but not to the structure or union directly.
*)

Inductive type : Type :=
  | Tvoid: type                                    (**r the [void] type *)
  | Tint: intsize -> signedness -> attr -> type    (**r integer types *)
  | Tfloat: floatsize -> attr -> type              (**r floating-point types *)
  | Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> type            (**r function types *)
  | Tstruct: ident -> fieldlist -> attr -> type    (**r struct types *)
  | Tunion: ident -> fieldlist -> attr -> type     (**r union types *)
  | Tcomp_ptr: ident -> attr -> type               (**r pointer to named struct or union *)

with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist

with fieldlist : Type :=
  | Fnil: fieldlist
  | Fcons: ident -> type -> fieldlist -> fieldlist.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}
with fieldlist_eq: forall (fld1 fld2: fieldlist), {fld1=fld2} + {fld1<>fld2}.
Proof.
  assert (forall (x y: intsize), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: signedness), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: attr), {x=y} + {x<>y}). decide equality. apply bool_dec.
  generalize ident_eq zeq. intros E1 E2. 
  decide equality.
  decide equality.
  generalize ident_eq. intros E1.
  decide equality.
Defined.

Opaque type_eq typelist_eq fieldlist_eq.

(** Extract the attributes of a type. *)

Definition attr_of_type (ty: type) :=
  match ty with
  | Tvoid => noattr
  | Tint sz si a => a
  | Tfloat sz a => a
  | Tpointer elt a => a
  | Tarray elt sz a => a
  | Tfunction args res => noattr
  | Tstruct id fld a => a
  | Tunion id fld a => a
  | Tcomp_ptr id a => a
  end.

Definition type_int32s := Tint I32 Signed noattr.
Definition type_bool := Tint IBool Signed noattr.

(** The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types. *)

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint I32 Unsigned _ => ty
  | Tint _ _ a          => Tint I32 Signed a
  | Tarray t sz a       => Tpointer t a
  | Tfunction _ _       => Tpointer ty noattr
  | _                   => ty
  end.

(** ** Expressions *)

(** Arithmetic and logical operators. *)

Inductive unary_operation : Type :=
  | Onotbool : unary_operation          (**r boolean negation ([!] in C) *)
  | Onotint : unary_operation           (**r integer complement ([~] in C) *)
  | Oneg : unary_operation.             (**r opposite (unary [-]) *)

Inductive binary_operation : Type :=
  | Oadd : binary_operation             (**r addition (binary [+]) *)
  | Osub : binary_operation             (**r subtraction (binary [-]) *)
  | Omul : binary_operation             (**r multiplication (binary [*]) *)
  | Odiv : binary_operation             (**r division ([/]) *)
  | Omod : binary_operation             (**r remainder ([%]) *)
  | Oand : binary_operation             (**r bitwise and ([&]) *)
  | Oor : binary_operation              (**r bitwise or ([|]) *)
  | Oxor : binary_operation             (**r bitwise xor ([^]) *)
  | Oshl : binary_operation             (**r left shift ([<<]) *)
  | Oshr : binary_operation             (**r right shift ([>>]) *)
  | Oeq: binary_operation               (**r comparison ([==]) *)
  | One: binary_operation               (**r comparison ([!=]) *)
  | Olt: binary_operation               (**r comparison ([<]) *)
  | Ogt: binary_operation               (**r comparison ([>]) *)
  | Ole: binary_operation               (**r comparison ([<=]) *)
  | Oge: binary_operation.              (**r comparison ([>=]) *)

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

(** Natural alignment of a type, in bytes. *)

Fixpoint alignof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => 4
  | Tarray t' _ _ => alignof t'
  | Tfunction _ _ => 1
  | Tstruct _ fld _ => alignof_fields fld
  | Tunion _ fld _ => alignof_fields fld
  | Tcomp_ptr _ _ => 4
  end

with alignof_fields (f: fieldlist) : Z :=
  match f with
  | Fnil => 1
  | Fcons id t f' => Zmax (alignof t) (alignof_fields f')
  end.

Scheme type_ind2 := Induction for type Sort Prop
  with fieldlist_ind2 := Induction for fieldlist Sort Prop.

Lemma alignof_1248:
  forall t, alignof t = 1 \/ alignof t = 2 \/ alignof t = 4 \/ alignof t = 8
with alignof_fields_1248:
  forall f, alignof_fields f = 1 \/ alignof_fields f = 2 \/ alignof_fields f = 4 \/ alignof_fields f = 8.
Proof.
  induction t; simpl; auto.
  destruct i; auto.
  destruct f; auto.
  induction f; simpl; auto.
  rewrite Zmax_spec. destruct (zlt (alignof_fields f) (alignof t)); auto.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  intros. generalize (alignof_1248 t). omega.
Qed.

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  intros. generalize (alignof_fields_1248 f). omega.
Qed.

(** Size of a type, in bytes. *)

Fixpoint sizeof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => 4
  | Tarray t' n _ => sizeof t' * Zmax 1 n
  | Tfunction _ _ => 1
  | Tstruct _ fld _ => align (Zmax 1 (sizeof_struct fld 0)) (alignof t)
  | Tunion _ fld _ => align (Zmax 1 (sizeof_union fld)) (alignof t)
  | Tcomp_ptr _ _ => 4
  end

with sizeof_struct (fld: fieldlist) (pos: Z) {struct fld} : Z :=
  match fld with
  | Fnil => pos
  | Fcons id t fld' => sizeof_struct fld' (align pos (alignof t) + sizeof t)
  end

with sizeof_union (fld: fieldlist) : Z :=
  match fld with
  | Fnil => 0
  | Fcons id t fld' => Zmax (sizeof t) (sizeof_union fld')
  end.

Lemma sizeof_pos:
  forall t, sizeof t > 0.
Proof.
  intro t0.
  apply (type_ind2 (fun t => sizeof t > 0)
                   (fun f => sizeof_union f >= 0 /\ forall pos, pos >= 0 -> sizeof_struct f pos >= 0));
  intros; simpl; auto; try omega.
  destruct i; omega.
  destruct f; omega.
  apply Zmult_gt_0_compat. auto. generalize (Zmax1 1 z); omega.
  destruct H. 
  generalize (align_le (Zmax 1 (sizeof_struct f 0)) (alignof_fields f) (alignof_fields_pos f)). 
  generalize (Zmax1 1 (sizeof_struct f 0)). omega. 
  generalize (align_le (Zmax 1 (sizeof_union f)) (alignof_fields f) (alignof_fields_pos f)). 
  generalize (Zmax1 1 (sizeof_union f)). omega. 
  split. omega. auto.
  destruct H0. split; intros.
  generalize (Zmax2 (sizeof t) (sizeof_union f)). omega.
  apply H1. 
  generalize (align_le pos (alignof t) (alignof_pos t)). omega.
Qed.

Lemma sizeof_struct_incr:
  forall fld pos, pos <= sizeof_struct fld pos.
Proof.
  induction fld; intros; simpl. omega. 
  eapply Zle_trans. 2: apply IHfld.
  apply Zle_trans with (align pos (alignof t)). 
  apply align_le. apply alignof_pos. 
  assert (sizeof t > 0) by apply sizeof_pos. omega.
Qed.

Lemma sizeof_alignof_compat:
  forall t, (alignof t | sizeof t).
Proof.
  induction t; simpl; try (apply Zdivide_refl).
  apply Zdivide_mult_l. auto.
  apply align_divides. apply alignof_fields_pos.
  apply align_divides. apply alignof_fields_pos.
Qed.

(** Byte offset for a field in a struct or union.
  Field are laid out consecutively, and padding is inserted
  to align each field to the natural alignment for its type. *)

Open Local Scope string_scope.

Fixpoint field_offset_rec (id: ident) (fld: fieldlist) (pos: Z)
                              {struct fld} : res Z :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' =>
      if ident_eq id id'
      then OK (align pos (alignof t))
      else field_offset_rec id fld' (align pos (alignof t) + sizeof t)
  end.

Definition field_offset (id: ident) (fld: fieldlist) : res Z :=
  field_offset_rec id fld 0.

Fixpoint field_type (id: ident) (fld: fieldlist) {struct fld} : res type :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' => if ident_eq id id' then OK t else field_type id fld'
  end.

(** Some sanity checks about field offsets.  First, field offsets are 
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall id ofs ty fld pos,
  field_offset_rec id fld pos = OK ofs -> field_type id fld = OK ty ->
  pos <= ofs /\ ofs + sizeof ty <= sizeof_struct fld pos.
Proof.
  intros until ty. induction fld; simpl.
  congruence.
  destruct (ident_eq id i); intros.
  inv H. inv H0. split. apply align_le. apply alignof_pos. apply sizeof_struct_incr.
  exploit IHfld; eauto. intros [A B]. split; auto. 
  eapply Zle_trans; eauto. apply Zle_trans with (align pos (alignof t)).
  apply align_le. apply alignof_pos. generalize (sizeof_pos t). omega. 
Qed.

Lemma field_offset_in_range:
  forall sid fld a fid ofs ty,
  field_offset fid fld = OK ofs -> field_type fid fld = OK ty ->
  0 <= ofs /\ ofs + sizeof ty <= sizeof (Tstruct sid fld a).
Proof.
  intros. exploit field_offset_rec_in_range; eauto. intros [A B].
  split. auto.  simpl. eapply Zle_trans. eauto.
  eapply Zle_trans. eapply Zle_max_r. apply align_le. apply alignof_fields_pos.
Qed.

(** Second, two distinct fields do not overlap *)

Lemma field_offset_no_overlap:
  forall id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  ofs1 + sizeof ty1 <= ofs2 \/ ofs2 + sizeof ty2 <= ofs1.
Proof.
  intros until ty2. intros fld0 A B C D NEQ.
  assert (forall fld pos,
  field_offset_rec id1 fld pos = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset_rec id2 fld pos = OK ofs2 -> field_type id2 fld = OK ty2 ->
  ofs1 + sizeof ty1 <= ofs2 \/ ofs2 + sizeof ty2 <= ofs1).
  induction fld; intro pos; simpl. congruence.
  destruct (ident_eq id1 i); destruct (ident_eq id2 i).
  congruence. 
  subst i. intros. inv H; inv H0.
  exploit field_offset_rec_in_range. eexact H1. eauto. tauto.  
  subst i. intros. inv H1; inv H2.
  exploit field_offset_rec_in_range. eexact H. eauto. tauto. 
  intros. eapply IHfld; eauto.

  apply H with fld0 0; auto.
Qed.

(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Fixpoint fieldlist_app (fld1 fld2: fieldlist) {struct fld1} : fieldlist :=
  match fld1 with
  | Fnil => fld2
  | Fcons id ty fld => Fcons id ty (fieldlist_app fld fld2)
  end.

Lemma field_offset_prefix:
  forall id ofs fld2 fld1,
  field_offset id fld1 = OK ofs ->
  field_offset id (fieldlist_app fld1 fld2) = OK ofs.
Proof.
  intros until fld2.
  assert (forall fld1 pos, 
    field_offset_rec id fld1 pos = OK ofs ->
    field_offset_rec id (fieldlist_app fld1 fld2) pos = OK ofs).
  induction fld1; intros pos; simpl. congruence.
  destruct (ident_eq id i); auto.
  intros. unfold field_offset; auto. 
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned:
  forall id fld ofs ty,
  field_offset id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof ty | ofs).
Proof.
  assert (forall id ofs ty fld pos,
          field_offset_rec id fld pos = OK ofs -> field_type id fld = OK ty ->
          (alignof ty | ofs)).
  induction fld; simpl; intros.
  discriminate.
  destruct (ident_eq id i). inv H; inv H0. 
  apply align_divides. apply alignof_pos. 
  eapply IHfld; eauto.
  intros. eapply H with (pos := 0); eauto.
Qed.

(** The [access_mode] function describes how a l-value of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the l-value using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the l-value (used for arrays and functions);
- [By_copy]: access is by reference, assignment is by copy
  (used for [struct] and [union] types)
- [By_nothing]: no access is possible, e.g. for the [void] type.
*)

Inductive mode: Type :=
  | By_value: memory_chunk -> mode
  | By_reference: mode
  | By_copy: mode
  | By_nothing: mode.

Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed _ => By_value Mint8signed
  | Tint I8 Unsigned _ => By_value Mint8unsigned
  | Tint I16 Signed _ => By_value Mint16signed
  | Tint I16 Unsigned _ => By_value Mint16unsigned
  | Tint I32 _ _ => By_value Mint32
  | Tint IBool _ _ => By_value Mint8unsigned
  | Tfloat F32 _ => By_value Mfloat32
  | Tfloat F64 _ => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ _ => By_value Mint32
  | Tarray _ _ _ => By_reference
  | Tfunction _ _ => By_reference
  | Tstruct _ _ _ => By_copy
  | Tunion _ _ _ => By_copy
  | Tcomp_ptr _ _ => By_nothing
end.

(** For the purposes of the semantics and the compiler, a type denotes
  a volatile access if it carries the [volatile] attribute and it is
  accessed by value. *)

Definition type_is_volatile (ty: type) : bool :=
  match access_mode ty with
  | By_value _ => attr_volatile (attr_of_type ty)
  | _          => false
  end.

(** Unroll the type of a structure or union field, substituting
    [Tcomp_ptr] by a pointer to the structure. *)

Section UNROLL_COMPOSITE.

Variable cid: ident.
Variable comp: type.

Fixpoint unroll_composite (ty: type) : type :=
  match ty with
  | Tvoid => ty
  | Tint _ _ _ => ty
  | Tfloat _ _ => ty
  | Tpointer t1 a => Tpointer (unroll_composite t1) a
  | Tarray t1 sz a => Tarray (unroll_composite t1) sz a
  | Tfunction t1 t2 => Tfunction (unroll_composite_list t1) (unroll_composite t2)
  | Tstruct id fld a => if ident_eq id cid then ty else Tstruct id (unroll_composite_fields fld) a
  | Tunion id fld a => if ident_eq id cid then ty else Tunion id (unroll_composite_fields fld) a
  | Tcomp_ptr id a => if ident_eq id cid then Tpointer comp a else ty
  end

with unroll_composite_list (tl: typelist) : typelist :=
  match tl with
  | Tnil => Tnil
  | Tcons t1 tl' => Tcons (unroll_composite t1) (unroll_composite_list tl')
  end

with unroll_composite_fields (fld: fieldlist) : fieldlist :=
  match fld with
  | Fnil => Fnil
  | Fcons id ty fld' => Fcons id (unroll_composite ty) (unroll_composite_fields fld')
  end.

Lemma alignof_unroll_composite:
  forall ty, alignof (unroll_composite ty) = alignof ty.
Proof.
  apply (type_ind2 (fun ty => alignof (unroll_composite ty) = alignof ty)
                   (fun fld => alignof_fields (unroll_composite_fields fld) = alignof_fields fld));
  simpl; intros; auto.
  destruct (ident_eq i cid); auto. 
  destruct (ident_eq i cid); auto. 
  destruct (ident_eq i cid); auto.
  decEq; auto.
Qed.

Lemma sizeof_unroll_composite:
  forall ty, sizeof (unroll_composite ty) = sizeof ty.
Proof.
Opaque alignof.
  apply (type_ind2 (fun ty => sizeof (unroll_composite ty) = sizeof ty)
                   (fun fld => 
                      sizeof_union (unroll_composite_fields fld) = sizeof_union fld
                   /\ forall pos,
                      sizeof_struct (unroll_composite_fields fld) pos = sizeof_struct fld pos));
  simpl; intros; auto.
  congruence.
  destruct H. rewrite <- (alignof_unroll_composite (Tstruct i f a)).
  simpl. destruct (ident_eq i cid); simpl. auto. rewrite H0; auto.
  destruct H. rewrite <- (alignof_unroll_composite (Tunion i f a)).
  simpl. destruct (ident_eq i cid); simpl. auto. rewrite H; auto.
  destruct (ident_eq i cid); auto.
  destruct H0. split. congruence.
  intros. rewrite alignof_unroll_composite. rewrite H1. rewrite H. auto.
Qed.

End UNROLL_COMPOSITE.

(** Classification of arithmetic operations and comparisons.
  The following [classify_] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  These functions are used to resolve
  overloading both in the dynamic semantics (module [Csem]), in the
  type system (module [Ctyping]), and in the compiler (module
  [Cshmgen]).
*)

Inductive classify_neg_cases : Type :=
  | neg_case_i(s: signedness)              (**r int *)
  | neg_case_f                             (**r float *)
  | neg_default.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned _ => neg_case_i Unsigned
  | Tint _ _ _ => neg_case_i Signed
  | Tfloat _ _ => neg_case_f
  | _ => neg_default
  end.

Inductive classify_notint_cases : Type :=
  | notint_case_i(s: signedness)              (**r int *)
  | notint_default.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned _ => notint_case_i Unsigned
  | Tint _ _ _ => notint_case_i Signed
  | _ => notint_default
  end.

(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of 
  the [!] and [?] operators, as well as the [if], [while], [for] statements. *)

Inductive classify_bool_cases : Type :=
  | bool_case_ip                          (**r integer or pointer *)
  | bool_case_f                           (**r float *)
  | bool_default.

Definition classify_bool (ty: type) : classify_bool_cases :=
  match typeconv ty with
  | Tint _ _ _ => bool_case_ip
  | Tpointer _ _ => bool_case_ip
  | Tfloat _ _ => bool_case_f
  | _ => bool_default
  end.

Inductive classify_add_cases : Type :=
  | add_case_ii(s: signedness)         (**r int, int *)
  | add_case_ff                        (**r float, float *)
  | add_case_if(s: signedness)         (**r int, float *)
  | add_case_fi(s: signedness)         (**r float, int *)
  | add_case_pi(ty: type)(a: attr)     (**r pointer, int *)
  | add_case_ip(ty: type)(a: attr)     (**r int, pointer *)
  | add_default.

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => add_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => add_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => add_case_ii Signed
  | Tfloat _ _, Tfloat _ _ => add_case_ff
  | Tint _ sg _, Tfloat _ _ => add_case_if sg
  | Tfloat _ _, Tint _ sg _ => add_case_fi sg
  | Tpointer ty a, Tint _ _ _ => add_case_pi ty a
  | Tint _ _ _, Tpointer ty a => add_case_ip ty a
  | _, _ => add_default
  end.

Inductive classify_sub_cases : Type :=
  | sub_case_ii(s: signedness)          (**r int , int *)
  | sub_case_ff                         (**r float , float *)
  | sub_case_if(s: signedness)          (**r int, float *)
  | sub_case_fi(s: signedness)          (**r float, int *)
  | sub_case_pi(ty: type)               (**r pointer, int *)
  | sub_case_pp(ty: type)               (**r pointer, pointer *)
  | sub_default.

Definition classify_sub (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => sub_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => sub_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => sub_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => sub_case_ff
  | Tint _ sg _, Tfloat _ _ => sub_case_if sg
  | Tfloat _ _, Tint _ sg _ => sub_case_fi sg
  | Tpointer ty _, Tint _ _ _ => sub_case_pi ty
  | Tpointer ty _ , Tpointer _ _ => sub_case_pp ty
  | _ ,_ => sub_default
  end.

Inductive classify_mul_cases : Type:=
  | mul_case_ii(s: signedness) (**r int , int *)
  | mul_case_ff                (**r float , float *)
  | mul_case_if(s: signedness) (**r int, float *)
  | mul_case_fi(s: signedness) (**r float, int *)
  | mul_default.

Definition classify_mul (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => mul_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => mul_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => mul_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => mul_case_ff
  | Tint _ sg _, Tfloat _ _ => mul_case_if sg
  | Tfloat _ _, Tint _ sg _ => mul_case_fi sg
  | _,_  => mul_default
end.

Inductive classify_div_cases : Type:=
  | div_case_ii(s: signedness) (**r int , int *)
  | div_case_ff                (**r float , float *)
  | div_case_if(s: signedness) (**r int, float *)
  | div_case_fi(s: signedness) (**r float, int *)
  | div_default.

Definition classify_div (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => div_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => div_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => div_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => div_case_ff
  | Tint _ sg _, Tfloat _ _ => div_case_if sg
  | Tfloat _ _, Tint _ sg _ => div_case_fi sg
  | _,_  => div_default
end.

(** The following is common to binary integer-only operators:
  modulus, bitwise "and", "or", and "xor". *)

Inductive classify_binint_cases : Type:=
  | binint_case_ii(s: signedness) (**r int , int *)
  | binint_default.

Definition classify_binint (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => binint_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => binint_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => binint_case_ii Signed
  | _,_  => binint_default
end.

(** The following is common to shift operators [<<] and [>>]. *)

Inductive classify_shift_cases : Type:=
  | shift_case_ii(s: signedness) (**r int , int *)
  | shift_default.

Definition classify_shift (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | _,_  => shift_default
end.

Inductive classify_cmp_cases : Type:=
  | cmp_case_ii(s: signedness) (**r int, int *)
  | cmp_case_pp                (**r pointer, pointer *)
  | cmp_case_ff                (**r float , float *)
  | cmp_case_if(s: signedness) (**r int, float *)
  | cmp_case_fi(s: signedness) (**r float, int *)
  | cmp_default.

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with 
  | Tint I32 Unsigned _ , Tint _ _ _ => cmp_case_ii Unsigned
  | Tint _ _ _ , Tint I32 Unsigned _ => cmp_case_ii Unsigned
  | Tint _ _ _ , Tint _ _ _ => cmp_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => cmp_case_ff
  | Tint _ sg _, Tfloat _ _ => cmp_case_if sg
  | Tfloat _ _, Tint _ sg _ => cmp_case_fi sg
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ _ _ => cmp_case_pp
  | Tint _ _ _, Tpointer _ _ => cmp_case_pp
  | _ , _ => cmp_default
  end.

Inductive classify_fun_cases : Type:=
  | fun_case_f (targs: typelist) (tres: type) (**r (pointer to) function *)
  | fun_default.

Definition classify_fun (ty: type) :=
  match ty with 
  | Tfunction args res => fun_case_f args res
  | Tpointer (Tfunction args res) _ => fun_case_f args res
  | _ => fun_default
  end.

Inductive classify_cast_cases : Type :=
  | cast_case_neutral                   (**r int|pointer -> int32|pointer *)
  | cast_case_i2i (sz2:intsize) (si2:signedness)   (**r int -> int *)
  | cast_case_f2f (sz2:floatsize)                  (**r float -> float *)
  | cast_case_i2f (si1:signedness) (sz2:floatsize) (**r int -> float *)
  | cast_case_f2i (sz2:intsize) (si2:signedness)   (**r float -> int *)
  | cast_case_ip2bool                   (**r int|pointer -> bool *)
  | cast_case_f2bool                    (**r float -> bool *)
  | cast_case_struct (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r struct -> struct *)
  | cast_case_union (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r union -> union *)
  | cast_case_void                                 (**r any -> void *)
  | cast_case_default.

Function classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  | Tint I32 si2 _, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_neutral
  | Tint IBool _ _, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_ip2bool
  | Tint IBool _ _, Tfloat _ _ => cast_case_f2bool
  | Tint sz2 si2 _, Tint sz1 si1 _ => cast_case_i2i sz2 si2
  | Tint sz2 si2 _, Tfloat sz1 _ => cast_case_f2i sz2 si2
  | Tfloat sz2 _, Tfloat sz1 _ => cast_case_f2f sz2
  | Tfloat sz2 _, Tint sz1 si1 _ => cast_case_i2f si1 sz2
  | Tpointer _ _, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_neutral
  | Tstruct id2 fld2 _, Tstruct id1 fld1 _ => cast_case_struct id1 fld1 id2 fld2
  | Tunion id2 fld2 _, Tunion id1 fld1 _ => cast_case_union id1 fld1 id2 fld2
  | Tvoid, _ => cast_case_void
  | _, _ => cast_case_default
  end.

(** Translating C types to Cminor types, function signatures,
  and external functions. *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tfloat _ _ => AST.Tfloat
  | _ => AST.Tint
  end.

Definition opttyp_of_type (t: type) : option AST.typ :=
  match t with
  | Tvoid => None
  | Tfloat _ _ => Some AST.Tfloat
  | _ => Some AST.Tint
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) : signature :=
  mksignature (typlist_of_typelist args) (opttyp_of_type res).


(** * Semantics of type-dependent operations *)

(** Semantics of casts.  [sem_cast v1 t1 t2 = Some v2] if value [v1],
  viewed with static type [t1], can be cast to type [t2],
  resulting in value [v2].  *)

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i 
  | I32, _ => i
  | IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one
  end.

Definition cast_int_float (si : signedness) (i: int) : float :=
  match si with
  | Signed => Float.floatofint i
  | Unsigned => Float.floatofintu i
  end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
  match si with
  | Signed => Float.intoffloat f
  | Unsigned => Float.intuoffloat f
  end.

Definition cast_float_float (sz: floatsize) (f: float) : float :=
  match sz with
  | F32 => Float.singleoffloat f
  | F64 => f
  end.

Function sem_cast (v: val) (t1 t2: type) : option val :=
  match classify_cast t1 t2 with
  | cast_case_neutral =>
      match v with
      | Vint _ | Vptr _ _ => Some v
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f sz2 =>
      match v with
      | Vfloat f => Some (Vfloat (cast_float_float sz2 f))
      | _ => None
      end
  | cast_case_i2f si1 sz2 =>
      match v with
      | Vint i => Some (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_ip2bool =>
      match v with
      | Vint i => Some (Vint (cast_int_int IBool Signed i))
      | Vptr _ _ => Some (Vint Int.one)
      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_struct id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
  | cast_case_union id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Function bool_val (v: val) (t: type) : option bool :=
  match v, t with
  | Vint n, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => Some (negb (Int.eq n Int.zero))
  | Vptr b ofs, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => Some true
  | Vfloat f, Tfloat sz _ => Some (negb(Float.cmp Ceq f Float.zero))
  | _, _ => None
  end.

(** The following [sem_] functions compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  For binary operations, the "usual binary conversions", adapted to a 32-bit
  platform, state that:
- If both arguments are of integer type, an integer operation is performed.
  For operations that behave differently at unsigned and signed types
  (e.g. division, modulus, comparisons), the unsigned operation is selected
  if at least one of the arguments is of type "unsigned int32", otherwise
  the signed operation is performed.
- If both arguments are of float type, a float operation is performed.
  We choose to perform all float arithmetic in double precision,
  even if both arguments are single-precision floats.
- If one argument has integer type and the other has float type,
  we convert the integer argument to float, then perform the float operation.
 *)

Function sem_neg (v: val) (ty: type) : option val :=
  match classify_neg ty with
  | neg_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | neg_default => None
  end.

Function sem_notint (v: val) (ty: type): option val :=
  match classify_notint ty with
  | notint_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.xor n Int.mone))
      | _ => None
      end
  | notint_default => None
  end.

Function sem_notbool (v: val) (ty: type) : option val :=
  match classify_bool ty with
  | bool_case_ip =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_default => None
  end.

Function sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with 
  | add_case_ii sg =>                   (**r integer addition *)
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
      | _,  _ => None
      end
  | add_case_ff =>                      (**r float addition *)
      match v1, v2 with
      | Vfloat n1, Vfloat n2 => Some (Vfloat (Float.add n1 n2))
      | _,  _ => None
      end
  | add_case_if sg =>                   (**r int plus float *)
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.add (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | add_case_fi sg =>                   (**r float plus int *)
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.add n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | add_case_pi ty _ =>                 (**r pointer plus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end   
  | add_case_ip ty _ =>                 (**r integer plus pointer *)
      match v1,v2 with
      | Vint n1, Vptr b2 ofs2 => 
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end   
  | add_default => None
end.

Function sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_ii sg =>            (**r integer subtraction *)
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
      | _,  _ => None
      end 
  | sub_case_ff =>               (**r float subtraction *)
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.sub f1 f2))
      | _,  _ => None
      end
  | sub_case_if sg =>            (**r int minus float *)
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.sub (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | sub_case_fi sg =>            (**r float minus int *)
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.sub n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | sub_case_pi ty =>            (**r pointer minus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
            Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if zeq b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default => None
  end.
 
Function sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
 match classify_mul t1 t2 with
  | mul_case_ii sg =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
      | _,  _ => None
      end
  | mul_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
      | _,  _ => None
      end
  | mul_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.mul (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | mul_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.mul n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | mul_default =>
      None
end.

Function sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
   match classify_div t1 t2 with
  | div_case_ii Unsigned =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
      | _,_ => None
      end
  | div_case_ii Signed =>
      match v1,v2 with
       | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint(Int.divs n1 n2))
      | _,_ => None
      end
  | div_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.div f1 f2))
      | _,  _ => None
      end 
  | div_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.div (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | div_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.div n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | div_default =>
      None
end.

Function sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii Unsigned =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
      | _, _ => None
      end
  | binint_case_ii Signed =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
      | _, _ => None
      end
  | binint_default =>
      None
  end.

Function sem_and (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.and n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_or (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.or n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_xor (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.xor n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_shl (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_shift t1 t2 with
  | shift_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
         if Int.ltu n2 Int.iwordsize then Some (Vint(Int.shl n1 n2)) else None
      | _, _ => None
      end
  | shift_default => None
  end.

Function sem_shr (v1: val) (t1: type) (v2: val) (t2: type): option val :=
  match classify_shift t1 t2 with 
  | shift_case_ii Unsigned =>
      match v1,v2 with 
      | Vint n1, Vint n2 =>
          if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shru n1 n2)) else None
      | _,_ => None
      end
   | shift_case_ii Signed =>
      match v1,v2 with
      | Vint n1,  Vint n2 =>
          if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shr n1 n2)) else None
      | _,  _ => None
      end
   | shift_default =>
      None
   end.

Function sem_cmp_mismatch (c: comparison): option val :=
  match c with
  | Ceq =>  Some Vfalse
  | Cne =>  Some Vtrue
  | _   => None
  end.

Function sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (valid_ptr: block -> Z -> bool): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_ii Signed =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmp c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ii Unsigned =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | _,  _ => None
      end
  | cmp_case_pp =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
          if valid_ptr b1 (Int.unsigned ofs1)
          && valid_ptr b2 (Int.unsigned ofs2) then
            if zeq b1 b2
            then Some (Val.of_bool (Int.cmpu c ofs1 ofs2))
            else sem_cmp_mismatch c
          else None
      | Vptr b ofs, Vint n =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | Vint n, Vptr b ofs =>
          if Int.eq n Int.zero then sem_cmp_mismatch c else None
      | _,  _ => None
      end
  | cmp_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Val.of_bool (Float.cmp c f1 f2))  
      | _,  _ => None
      end
  | cmp_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Val.of_bool (Float.cmp c (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | cmp_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Val.of_bool (Float.cmp c n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | cmp_default => None
  end.

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Onotint => sem_notint v ty
  | Oneg => sem_neg v ty
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (valid_ptr: block -> Z -> bool): option val :=
  match op with
  | Oadd => sem_add v1 t1 v2 t2
  | Osub => sem_sub v1 t1 v2 t2 
  | Omul => sem_mul v1 t1 v2 t2
  | Omod => sem_mod v1 t1 v2 t2
  | Odiv => sem_div v1 t1 v2 t2 
  | Oand => sem_and v1 t1 v2 t2
  | Oor  => sem_or v1 t1 v2 t2
  | Oxor  => sem_xor v1 t1 v2 t2
  | Oshl => sem_shl v1 t1 v2 t2
  | Oshr  => sem_shr v1 t1 v2 t2   
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 valid_ptr
  | One => sem_cmp Cne v1 t1 v2 t2 valid_ptr
  | Olt => sem_cmp Clt v1 t1 v2 t2 valid_ptr
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 valid_ptr
  | Ole => sem_cmp Cle v1 t1 v2 t2 valid_ptr
  | Oge => sem_cmp Cge v1 t1 v2 t2 valid_ptr
  end.

(** Common-sense relations between boolean operators *)

Lemma cast_bool_bool_val:
  forall v t,
  sem_cast v t (Tint IBool Signed noattr) =
  match bool_val v t with None => None | Some b => Some(Val.of_bool b) end.
Proof.
  intros. unfold sem_cast, bool_val. destruct t; simpl; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto. 
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
Qed.

Lemma notbool_bool_val:
  forall v t,
  sem_notbool v t =
  match bool_val v t with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof.
  assert (CB: forall i s a, classify_bool (Tint i s a) = bool_case_ip).
    intros. destruct i; auto. destruct s; auto. 
  intros. unfold sem_notbool, bool_val. destruct t; try rewrite CB; simpl; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto. 
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
Qed.
