Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.simple_reify.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.Zlength_solver.

Definition int_signed_or_unsigned (t: type) : int -> Z :=
  match typeconv t with
  | Tint _ Signed _ => Int.signed
  | Tint _ Unsigned _ => Int.unsigned
  | _ => fun _ => 0 (* bogus *)
  end.

Section SIMPL_REPTYPE.

Context {cs: compspecs}.

(* We assume type and gfield list are compatible. *)

Definition is_effective_array (t: type) (n: Z) (a: attr) (i: Z) (v: reptype_skeleton) : option reptype_skeleton := None.

Fixpoint is_effective_struct i (m: members) (v: reptype_skeleton) : option reptype_skeleton :=
  match m with
  | nil => None
  | _ :: nil => Some v
  | (i', _) :: tl =>
    match v with
    | RepPair v1 v2 => if (ident_eq i i') then Some v1 else is_effective_struct i tl v2
    | _ => None
    end
  end.

Fixpoint is_effective_union i (m: members) (v: reptype_skeleton) : option reptype_skeleton :=
  match m with
  | nil => None
  | _ :: nil => Some v
  | (i', _) :: tl =>
    match v with
    | RepInl v0 => if (ident_eq i i') then Some v0 else None
    | RepInr v0 => if (ident_eq i i') then None else is_effective_union i tl v0
    | _ => None
    end
  end.

Definition is_effective (t: type) (gf: gfield) (v: reptype_skeleton) : option reptype_skeleton :=
  match t, gf with
  | Tarray t0 hi a, ArraySubsc i => is_effective_array t0 hi a i v
  | Tstruct id _, StructField i => is_effective_struct i (co_members (get_co id)) v
  | Tunion id _, UnionField i => is_effective_union i (co_members (get_co id)) v
  | _, _ => None
  end.

(*
(*
Currently, array type data are treated as a string of data. In fact,
they can also be treated as sets of data or other forms of collection
of data. User should choose the way to specify that. However, we
treated them as string and simplify the expression in this way as
default. In the future, this default should be deleted.
*)

Fixpoint extra_simpl_len (rgfs: list gfield) : nat :=
  match rgfs with
  | ArraySubsc _ :: rgfs0 => S (extra_simpl_len rgfs0)
  | _ => 0%nat
  end.

Fixpoint effective_len_rec (t: type) (rgfs: list gfield) (v: reptype_skeleton) : nat :=
  match rgfs with
  | nil => 0%nat
  | gf :: rgfs0 =>
     match is_effective t gf v with
     | Some v0 => S (effective_len_rec (gfield_type t gf) rgfs0 v0)
     | None => extra_simpl_len rgfs
     end
  end.

Fixpoint effective_len (t: type) (gfs: list gfield) (v: reptype_skeleton) : nat
  := effective_len_rec t (rev gfs) v.
*)

(* This is how we control the length of computation. *)
Definition effective_len (t: type) (gfs: list gfield) (v: reptype_skeleton) : nat
  := length gfs.

End SIMPL_REPTYPE.

Ltac firstn_tac A n l :=
  match n with
    | 0%nat => constr:(@nil A)
    | S ?n0 => match l with
               | @nil A => constr: (@nil A)
               | @cons A ?a ?l => let res := firstn_tac A n0 l in constr: (@cons A a res)
             end
  end.

Ltac skipn_tac A n l :=
  match n with
    | 0%nat => constr: (l)
    | S ?n0 => match l with
               | @nil A => constr: (@nil A)
               | @cons A ?a ?l => let res := skipn_tac A n0 l in constr: (res)
             end
  end.

Ltac remember_indexes gfs :=
  match gfs with
  | ArraySubsc ?i :: ?g' => remember i; remember_indexes g'
  | _ :: ?g' => remember_indexes g'
  | nil => idtac
  end.

Ltac solve_load_rule_evaluation_old :=
  clear;
  repeat
  match goal with
  | A : _ |- _ => clear A
  | A := _ |- _ => clear A
  end;
  match goal with
  | |- JMeq (@proj_reptype _ _ ?name_of_gfs ?name_of_v) _ =>
    subst name_of_gfs;
    try subst name_of_v
  end;
  match goal with
  | |- JMeq (@proj_reptype _ _ ?gfs _) _ =>
    remember_indexes gfs
  end;
  match goal with
  | |- JMeq (@proj_reptype ?cs ?t ?gfs ?v) _ =>
    let s := simple_reify.simple_reify v in
    let len_opaque := eval vm_compute in (length gfs - effective_len t gfs s)%nat in
    let gfs_opaque := (firstn_tac gfield len_opaque gfs) in
    let gfs_compute := (skipn_tac gfield len_opaque gfs) in
    match gfs_opaque with
    | nil =>
      let opaque_function := fresh "opaque_function" in
      let opaque_v := fresh "v" in
      (* TODO: the next line seems unuseful *)
      pose (proj_reptype (nested_field_type t gfs_compute) gfs_opaque) as opaque_function;
      set (opaque_v := v);
      lazy beta zeta iota delta - [opaque_v sublist.Znth Int.repr];
      subst opaque_v; subst; apply JMeq_refl
    | @cons _ _ _ =>
      (* TODO: this part needs debug *)
      let opaque_function := fresh "opaque_function" in
      let opaque_v := fresh "v" in
      pose (proj_reptype (nested_field_type t gfs_compute) gfs_opaque) as opaque_function;
      set (opaque_v := v);
      lazy beta zeta iota delta - [opaque_function opaque_v sublist.Znth Int.repr];
      subst opaque_v opaque_function; subst; apply JMeq_refl
    end
  end.

(* Warning: these aren't defined until later, which should be OK,
  but might be confusing. 
Instance Inhabitant_val : Inhabitant val := Vundef.
Instance Inhabitant_int: Inhabitant int := Int.zero.
*)

(* Given a JMEq containing the result of a load, pulls the "Vint" out of "map".
   Useful for all loads from int arrays.
   Makes entailer and other tactics more successful. *)
Ltac default_canon_load_result :=
  repeat (
    first [ rewrite Znth_map_Vbyte
          | rewrite (@Znth_map int _)
          | rewrite (@Znth_map int64 _)
          | rewrite (@Znth_map val _)
          | rewrite (@Znth_map Z _) ];
    [ | solve [auto; Zlength_solve] + match goal with
        | |- ?Bounds => fail 10 "Make sure Zlength_solve or auto can prove" Bounds
"
The usual way to do that is to use assert or assert_PROP before forward."
        end  ]
  );
      repeat match goal with
            | |- context [fst(?A,?B)] => change (fst(A,B)) with A
            | |- context [snd(?A,?B)] => change (snd(A,B)) with B
            end.

Ltac canon_load_result := default_canon_load_result.

(* BEGIN:  Big hack just to make sure that certain instances of [fst] and [snd] are not
 simplified by solve_load_rule_evaluation and solve_store_rule_evaluation *)

Definition myfst {A}{B} (x: A*B) : A := match x with (y,z) => y end.
Definition mysnd {A}{B} (x: A*B) : B := match x with (y,z) => z end.

Definition proj_compact_prod' {A: Type} {F: A -> Type} (a: A) (l: list A) (v: compact_prod (map F l)) (default: F a) (H: forall a b: A, {a = b} + {a <> b}) : F a.
Proof.
  destruct l; [exact default |].
  revert a0 v; induction l; intros.
  + destruct (H a a0).
    - subst.
      exact v.
    - exact default.
  + destruct (H a a1).
    - subst.
      exact (myfst v).
    - exact (IHl a0 (mysnd v)).
Defined.

Definition upd_compact_prod' {A} {F} (l: list A) (v: compact_prod (map F l)) (a: A) (v0: F a) (H: forall a b: A, {a = b} + {a <> b}) : compact_prod (map F l).
Proof.
  intros.
  destruct l; [exact v |].
  revert a0 v; induction l; intros.
  + destruct (H a a0).
    - subst.
      exact v0.
    - exact v.
  + destruct (H a a1).
    - subst.
      exact (v0, (mysnd v)).
    - exact ((myfst v), IHl a0 (mysnd v)).
Defined.

Definition proj_struct' (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_prod' (i, field_type i m) m v d member_dec.

Definition upd_gfield_reptype' {cs: compspecs} t gf (v: reptype t) (v0: reptype (gfield_type t gf)) : reptype t :=
  fold_reptype
  (match t, gf return (REPTYPE t -> reptype (gfield_type t gf) -> REPTYPE t)
  with
  | Tarray t0 n a, ArraySubsc i => upd_Znth i
(*zl_concat (zl_concat (zl_sublist 0 i v) (zl_singleton i v0)) (zl_sublist (i + 1) n v) *)
  | Tstruct id _, StructField i =>
      fun v v0 => upd_compact_prod' _ v (i, field_type i (co_members (get_co id))) v0 member_dec
  | Tunion id _, UnionField i =>
      fun v v0 => upd_compact_sum _ v (i, field_type i (co_members (get_co id))) v0 member_dec
  | _, _ => fun v _ => v
  end (unfold_reptype v) v0).

Definition proj_gfield_reptype' {cs: compspecs} (t: type) (gf: gfield) (v: reptype t): reptype (gfield_type t gf) :=
  match t, gf return (REPTYPE t -> reptype (gfield_type t gf))
  with
  | Tarray t0 hi a, ArraySubsc i => fun v => @Znth _ (default_val _) i v
  | Tstruct id _, StructField i => fun v => proj_struct i (co_members (get_co id)) v (default_val _)
  | Tunion id _, UnionField i => fun v => proj_union i (co_members (get_co id)) v (default_val _)
  | _, _ => fun _ => default_val _
  end (unfold_reptype v).

Section A.
Context {cs: compspecs}.
Fixpoint proj_reptype'  (t: type) (gfs: list gfield) (v: reptype t) : reptype (nested_field_type t gfs) :=
  let res :=
  match gfs as gfs'
    return reptype (match gfs' with
                    | nil => t
                    | gf :: gfs0 => gfield_type (nested_field_type t gfs0) gf
                    end)
  with
  | nil => v
  | gf :: gfs0 => proj_gfield_reptype' _ gf (proj_reptype' t gfs0 v)
  end
  in eq_rect_r reptype res (nested_field_type_ind t gfs).

Fixpoint upd_reptype' (t: type) (gfs: list gfield) (v: reptype t) (v0: reptype (nested_field_type t gfs)): reptype t :=
  match gfs as gfs'
    return reptype (match gfs' with
                    | nil => t
                    | gf :: gfs0 => gfield_type (nested_field_type t gfs0) gf
                    end) -> reptype t
  with
  | nil => fun v0 => v0
  | gf :: gfs0 => fun v0 => upd_reptype' t gfs0 v (upd_gfield_reptype' _ gf (proj_reptype t gfs0 v) v0)
  end (eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t gfs))).
End A.

Lemma test_equal_proj_reptype': False.
unify @proj_reptype @proj_reptype'.
unify @upd_reptype @upd_reptype'.
Abort.

(* END:  Big hack just to make sure that certain instances of [fst] and [snd] are not... *)
Ltac solve_load_rule_evaluation :=
  eapply JMeq_trans;
  [ clear;
    repeat
    match goal with
    | A : _ |- _ => clear A 
    | A := _ |- _ => clear A 
    end;
    match goal with
    | |- JMeq (@proj_reptype _ _ ?gfs _) _ =>
      remember_indexes gfs
    end;
    match goal with
    | |- JMeq (@proj_reptype ?cs ?t ?gfs ?v) _ =>
        let opaque_v := fresh "opaque_v" in
              remember v as opaque_v;
              change proj_reptype with proj_reptype';
              cbv - [ sublist.Znth Int.repr JMeq myfst mysnd];
              change @myfst with @fst;
              change @mysnd with @snd;
              subst opaque_v;
              repeat match goal with
                     | |- context [@fst ?a ?b (?c,?d)] =>
                              let u := eval hnf in (@fst a b (c,d)) in
                                 change_no_check (@fst a b (c,d)) with c
                     | |- context [@snd ?a ?b (?c,?d)] =>
                               let u := eval hnf in (@snd a b (c,d)) in
                                  change_no_check (@snd a b (c,d)) with d
                    end

        end;
        subst; apply JMeq_refl
  | canon_load_result; apply JMeq_refl ].

Ltac simplify_casts := 
  cbv beta iota delta [ Cop.cast_int_int  Cop.cast_int_float Cop.cast_float_int  Cop.cast_int_single Cop.cast_single_int
                  Cop.cast_int_long Cop.cast_long_float Cop.cast_long_single Cop.cast_float_long Cop.cast_single_long ];
 rewrite ?sign_ext_inrange 
  by (let z := fresh "z" in set (z := two_p (Zpos _ - 1)); compute in z; subst z;
          rewrite Int.signed_repr by rep_lia;  rep_lia).

Lemma cons_congr: forall {A} (a a': A) bl bl',
  a=a' -> bl=bl' -> a::bl = a'::bl'.
Proof.
intros; f_equal; auto.
Qed.

Ltac subst_indexes gfs :=
  match gfs with
  | ArraySubsc ?i :: ?g' => 
     match goal with H: ?x = i |- _ => is_var x; subst x; subst_indexes g' end
  | _ :: ?g' => subst_indexes g'
  | nil => idtac
  end.

Ltac solve_store_rule_evaluation :=
  match goal with |- upd_reptype ?t ?gfs ?v0 ?v1 = ?B =>
   let rhs := fresh "rhs" in set (rhs := B);
  match type of rhs with ?A =>
   let a := fresh "a" in set (a:=A) in rhs; 
    lazy beta zeta iota delta [reptype reptype_gen] in a;
    cbn in a; subst a
  end;
   let h0 := fresh "h0" in let h1 := fresh "h1" in
   set (h0:=v0); set (h1:=v1); change (upd_reptype t gfs h0 h1 = rhs);
   remember_indexes gfs;
   let j := fresh "j" in match type of h0 with ?J => set (j := J) in h0 end;
   lazy beta zeta iota delta in j; subst j;
   change @upd_reptype with @upd_reptype';
   cbv - [rhs h0 h1 Znth upd_Znth Zlength myfst mysnd];
   change @myfst with @fst;
   change @mysnd with @snd;
   try unfold v1 in h1;
   revert h1; simplify_casts; cbv zeta;
   subst rhs h0; subst_indexes gfs;
  repeat match goal with
            | |- context [fst (@pair ?t1 ?t2 ?A ?B)] => change (fst(@pair t1 t2 A B)) with A
            | |- context [snd(@pair ?t1 ?t2 ?A ?B)] => change (snd(@pair t1 t2 A B)) with B
            | |-  context [@pair ?t1 ?t2 _ _] => 
                      let u1 := eval compute in t1 in
                      let u2 := eval compute in t2 in
                      progress (change_no_check t1 with u1; change_no_check t2 with u2)
            end;
  apply eq_refl
  end.
