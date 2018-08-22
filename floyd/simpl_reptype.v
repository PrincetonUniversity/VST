Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.simple_reify.

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
    | RepInr v0 => if (ident_eq i i') then None else is_effective_struct i tl v0
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
Fixpoint effective_len (t: type) (gfs: list gfield) (v: reptype_skeleton) : nat
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
    [ | solve [auto; list_solve] + match goal with
        | |- ?Bounds => fail 1000 "Make sure list_solve or auto can prove" Bounds
        end  ]
  ).

Ltac canon_load_result := default_canon_load_result.

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
        set (opaque_v := v);
        cbv - [opaque_v sublist.Znth Int.repr JMeq];
        subst opaque_v; subst; apply JMeq_refl
    end
  | canon_load_result; apply JMeq_refl ].

Ltac simplify_casts := 
  cbv beta iota delta [ Cop.cast_int_int  Cop.cast_int_float Cop.cast_float_int  Cop.cast_int_single Cop.cast_single_int
                  Cop.cast_int_long Cop.cast_long_float Cop.cast_long_single Cop.cast_float_long Cop.cast_single_long ];
 rewrite ?sign_ext_inrange 
  by (let z := fresh "z" in set (z := two_p (Zpos _ - 1)); compute in z; subst z;
          rewrite Int.signed_repr by rep_omega;  rep_omega).

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
   lazy beta zeta iota delta [reptype reptype_gen] in rhs;
   simpl in rhs;
   let h0 := fresh "h0" in let h1 := fresh "h1" in
   set (h0:=v0); set (h1:=v1); change (upd_reptype t gfs h0 h1 = rhs);
   remember_indexes gfs;
   let j := fresh "j" in match type of h0 with ?J => set (j := J) in h0 end;
   lazy beta zeta iota delta in j; subst j;
   lazy beta zeta iota delta - [rhs h0 h1 upd_Znth Zlength];
   try unfold v1 in h1;
   revert h1; simplify_casts; cbv zeta;
   subst rhs h0; subst_indexes gfs;
  apply eq_refl
  end.
