Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.aggregate_type.
Require Import VST.zlist.sublist.

Section PROJ_REPTYPE.

Context {cs: compspecs}.

Definition field_type_name_member 
  {i: ident} {m: members} (t: reptype (field_type (name_member (get_member i m)) m)) : 
   reptype (field_type i m).
rewrite name_member_get in t. apply t.
Defined.

Definition proj_gfield_reptype (t: type) (gf: gfield) (v: reptype t): reptype (gfield_type t gf) :=
  match t, gf return (REPTYPE t -> reptype (gfield_type t gf))
  with
  | Tarray t0 hi a, ArraySubsc i => fun v => @Znth _ (default_val _) i v
  | Tstruct id _, StructField i =>
      fun v => field_type_name_member (proj_struct i (co_members (get_co id)) v (default_val _))
  | Tunion id _, UnionField i => 
      fun v => field_type_name_member (proj_union i (co_members (get_co id)) v (default_val _))
  | _, _ => fun _ => default_val _
  end (unfold_reptype v).


Fixpoint proj_reptype (t: type) (gfs: list gfield) (v: reptype t) : reptype (nested_field_type t gfs) :=
  let res :=
  match gfs as gfs'
    return reptype (match gfs' with
                    | nil => t
                    | gf :: gfs0 => gfield_type (nested_field_type t gfs0) gf
                    end)
  with
  | nil => v
  | gf :: gfs0 => proj_gfield_reptype _ gf (proj_reptype t gfs0 v)
  end
  in eq_rect_r reptype res (nested_field_type_ind t gfs).

End PROJ_REPTYPE.

