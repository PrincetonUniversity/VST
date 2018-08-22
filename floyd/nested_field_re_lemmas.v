(* TODO: remove this file. Not useful at all. *)
Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.aggregate_type.

(*
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.entailer.
Require Import VST.floyd.closed_lemmas.
*)
Local Open Scope logic.

(**********************************************

nf_sub2: substraction in type
proj_except_reptype: big reptype value
proj_reptype: small reptype value
pair_reptype: reversion of proj/PROJ
upd_reptype
data_at_with_exception
data_at_with_exception * field_at = data_at

Comment: for now, ident_eq will be used throughout all these definition
because it is used in field_type and field_offset in compcert. However,
it should be replaced by Pos.eqb here and in compcert.

Further plan: multi substraction, which is useful for definion tree structure

mnf_sub: substraction in type
mproj_except_reptype: big reptype value
mproj_reptype: small reptype value
mnf_pair_reptype: reversion of proj/PROJ
mupd_reptype
data_at_with_mexception
data_at_with_mexception * [field_at] = data_at

**********************************************)

(*** reptype level ***)

(*
Fixpoint proj_reptype_structlist id f ofs (v: reptype_structlist f) :
  reptype (match field_offset_rec id f ofs, field_type id f with
           | Errors.OK _, Errors.OK t0 => t0
           | _, _ => Tvoid
           end) :=
  match f as f'
    return reptype_structlist f' -> reptype (match field_offset_rec id f' ofs, field_type id f' with
                                             | Errors.OK _, Errors.OK t0 => t0
                                             | _, _ => Tvoid
                                             end) with
  | Fnil => fun _ => default_val _
  | Fcons i0 t0 flds0 =>
    if is_Fnil flds0 as b
      return ((if b then reptype t0 else reptype t0 * reptype_structlist flds0) ->
              reptype (match (if ident_eq id i0
                             then Errors.OK (align ofs (alignof t0))
                             else field_offset_rec id flds0 (align ofs (alignof t0) + sizeof t0)),
                             (if ident_eq id i0 then Errors.OK t0 else field_type id flds0)
                       with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end))
    then fun v =>
      if ident_eq id i0 as b0
        return reptype (match (if b0
                             then Errors.OK (align ofs (alignof t0))
                             else field_offset_rec id flds0 (align ofs (alignof t0) + sizeof t0)),
                             (if b0 then Errors.OK t0 else field_type id flds0)
                        with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end)
      then v
      else default_val _
    else fun v =>
      if ident_eq id i0 as b0
        return reptype (match (if b0
                             then Errors.OK (align ofs (alignof t0))
                             else field_offset_rec id flds0 (align ofs (alignof t0) + sizeof t0)),
                             (if b0 then Errors.OK t0 else field_type id flds0)
                        with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end)
      then fst v
      else proj_reptype_structlist id flds0 (align ofs (alignof t0) + sizeof t0) (snd v)
  end v.

Fixpoint proj_reptype_unionlist id f (v: reptype_unionlist f) :
  reptype (match field_type id f with
           | Errors.OK t0 => t0
           | _ => Tvoid
           end) :=
  match f as f'
    return reptype_unionlist f' -> reptype (match field_type id f' with
                                            | Errors.OK t0 => t0
                                            | _ => Tvoid
                                            end) with
  | Fnil => fun _ => default_val _
  | Fcons i0 t0 flds0 =>
    if is_Fnil flds0 as b
      return ((if b then reptype t0 else reptype t0 + reptype_unionlist flds0) ->
              reptype (match (if ident_eq id i0 then Errors.OK t0 else field_type id flds0) with
                       | Errors.OK t0 => t0
                       | _ => Tvoid
                       end))
    then fun v =>
      if ident_eq id i0 as b0
        return reptype (match (if b0 then Errors.OK t0 else field_type id flds0) with
                        | Errors.OK t0 => t0
                        | _ => Tvoid
                        end)
      then v
      else default_val _
    else fun v =>
      if ident_eq id i0 as b0
        return reptype (match (if b0 then Errors.OK t0 else field_type id flds0) with
                        | Errors.OK t0 => t0
                        | _ => Tvoid
                        end)
      then match v with
           | inl v0 => v0
           | _ => default_val _
           end
      else match v with
           | inr v0 => proj_reptype_unionlist id flds0 v0
           | _ => default_val _
           end
  end v.
*)


Definition proj_except_reptype (t: type) (g

Lemma gupd_reptype_structlist_aux: forall f i0 t0,
  all_fields_replace_one2 f i0 t0 = match f with
                                    | Fnil => Fnil
                                    | Fcons i1 t1 flds0 =>
                                      if ident_eq i0 i1
                                      then Fcons i1 t0 flds0
                                      else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0)
                                    end.
Proof.
  intros.
  destruct f; [|simpl; if_tac]; reflexivity.
Defined.

Definition gupd_reptype_array t1 n a (i: Z) (t0: type) (v: list (reptype t1)) (v0: reptype t0) : reptype_structlist (ArrayField t1 n a i t0) :=
  if Z.eqb i 0 as b
    return reptype_structlist
             (if b
              then Fcons 1002%positive t0
                     (Fcons 1003%positive (Tarray t1 (n - 1) a) Fnil)
              else
                if (Z.eqb i (n - 1))
                then Fcons 1001%positive (Tarray t1 (n - 1) a)
                       (Fcons 1002%positive t0 Fnil)
                else Fcons 1001%positive (Tarray t1 i a)
                       (Fcons 1002%positive t0
                          (Fcons 1003%positive (Tarray t1 (n - i - 1) a) Fnil)))
  then (v0, skipn 1%nat v)
  else
    if Z.eqb i (n - 1) as b0
      return reptype_structlist
               (if b0
                then Fcons 1001%positive (Tarray t1 (n - 1) a)
                       (Fcons 1002%positive t0 Fnil)
                else Fcons 1001%positive (Tarray t1 i a)
                       (Fcons 1002%positive t0
                          (Fcons 1003%positive (Tarray t1 (n - i - 1) a) Fnil)))
    then (v, v0)
    else (v, (v0, skipn (nat_of_Z (i + 1)) v)).

Fixpoint gupd_reptype_structlist f (i0: ident) (t0: type) (v: reptype_structlist f) (v0: reptype t0) : reptype_structlist (all_fields_replace_one2 f i0 t0) :=
  let res :=
  match f as f'
    return reptype_structlist f' ->
           reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i1 t1 flds0 =>
                                 if ident_eq i0 i1
                                 then Fcons i1 t0 flds0
                                 else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0)
                               end)
  with
  | Fnil => fun _ => struct_default_val _
  | Fcons i1 t1 flds0 => fun v =>
   (if ident_eq i0 i1 as b
      return reptype_structlist (if b
                                 then Fcons i1 t0 flds0
                                 else Fcons i1 t1 (all_fields_replace_one2 flds0 i0 t0))
    then
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t1 else reptype t1 * reptype_structlist flds0) ->
               (if b0 then reptype t0 else reptype t0 * reptype_structlist flds0)
      then fun _ => v0
      else fun v => (v0, snd v)
     ) v
    else
     (if is_Fnil flds0 as b0
        return (if b0 then reptype t1 else reptype t1 * reptype_structlist flds0) ->
               (if is_Fnil (all_fields_replace_one2 flds0 i0 t0) then reptype t1 else reptype t1 *
                   reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
      then
        if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b1
          return reptype t1 ->
                 (if b1 then reptype t1 else reptype t1 *
                     reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
        then fun v => v
        else fun _ => (default_val _, struct_default_val _) (* impossible situation *)
      else
        if is_Fnil (all_fields_replace_one2 flds0 i0 t0) as b1
          return reptype t1 * reptype_structlist flds0 ->
                 (if b1 then reptype t1 else reptype t1 *
                     reptype_structlist (all_fields_replace_one2 flds0 i0 t0))
        then fun _ => default_val _
        else fun v => (fst v, gupd_reptype_structlist flds0 i0 t0 (snd v) v0)
      ) v
   )
  end v
  in
  eq_rect_r reptype_structlist res (gupd_reptype_structlist_aux f i0 t0).

Definition gupd_reptype_unionlist (i0: ident) (t0: type) (v0: reptype t0) : reptype_unionlist (Fcons i0 t0 Fnil) := v0.

Fixpoint gupd_reptype (t: type) (gfs: list gfield) (t0: type) (v: reptype t) (v0: reptype t0): reptype (nf_replace2 t gfs t0) :=
  match gfs as gfs' return reptype (nf_replace2 t gfs' t0) with
  | nil => v0
  | ArraySubsc i :: gfs0 =>
      match nested_field_type2 t gfs0 as T
        return reptype T ->
               reptype (match T with
                        | Tarray t1 n a =>
                          nf_replace2 t gfs0
                            (Tstruct 1000%positive (ArrayField t1 n a i t0) noattr)
                        | _ => t
                        end)
      with
      | Tarray t1 n a =>
        fun v1 => gupd_reptype t gfs0 (Tstruct 1000%positive (ArrayField t1 n a i t0) noattr) v
                    (gupd_reptype_array t1 n a i t0 v1 v0)
      | _ => fun _ => default_val _
      end (proj_reptype t gfs0 v)
  | StructField i :: gfs0 =>
    match nested_field_type2 t gfs0 as T
      return reptype T -> reptype (match T with
                                   | Tstruct i0 f a => nf_replace2 t gfs0
                                     (Tstruct i0 (all_fields_replace_one2 f i t0) a)
                                   | _ => t
                                   end)
    with
    | Tstruct i0 f a => fun v1 => gupd_reptype t gfs0 (Tstruct i0 (all_fields_replace_one2 f i t0) a) v
                                 (gupd_reptype_structlist f i t0 v1 v0)
    | _ => fun _ => default_val _
    end (proj_reptype t gfs0 v)
  | UnionField i :: gfs0 =>
    match nested_field_type2 t gfs0 as T
      return reptype T -> reptype (match T with
                                   | Tunion i0 f a => nf_replace2 t gfs0
                                     (Tunion i0 (Fcons i t0 Fnil) a)
                                   | _ => t
                                   end)
    with
    | Tunion i0 f a => fun _ => gupd_reptype t gfs0 (Tunion i0 (Fcons i t0 Fnil)a) v
                                 (gupd_reptype_unionlist i t0 v0)
    | _ => fun _ => default_val _
    end (proj_reptype t gfs0 v)
  end.

Definition proj_except_reptype_array t1 n a (i: Z) (v: list (reptype t1)) : reptype_structlist (all_fields_except_one2 (ArrayField t1 n a i Tvoid) 1002%positive):=
  if Z.eqb i 0 as b
    return reptype_structlist (all_fields_except_one2
             (if b
              then Fcons 1002%positive Tvoid
                     (Fcons 1003%positive (Tarray t1 (n - 1) a) Fnil)
              else
                if (Z.eqb i (n - 1))
                then Fcons 1001%positive (Tarray t1 (n - 1) a)
                       (Fcons 1002%positive Tvoid Fnil)
                else Fcons 1001%positive (Tarray t1 i a)
                       (Fcons 1002%positive Tvoid
                          (Fcons 1003%positive (Tarray t1 (n - i - 1) a) Fnil)))
             1002%positive)
  then skipn 1%nat v
  else
    if Z.eqb i (n - 1) as b0
      return reptype_structlist (all_fields_except_one2
               (if b0
                then Fcons 1001%positive (Tarray t1 (n - 1) a)
                       (Fcons 1002%positive Tvoid Fnil)
                else Fcons 1001%positive (Tarray t1 i a)
                       (Fcons 1002%positive Tvoid
                          (Fcons 1003%positive (Tarray t1 (n - i - 1) a) Fnil)))
               1002%positive)
    then v
    else (v, skipn (nat_of_Z (i + 1)) v).

Fixpoint proj_except_reptype_structlist (f: fieldlist) (id: ident) (v: reptype_structlist f): reptype_structlist (all_fields_except_one2 f id) :=
  let res :=
  match f as f'
    return reptype_structlist f' ->
           reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i t f0 =>
                                   if ident_eq id i
                                   then f0
                                   else Fcons i t (all_fields_except_one2 f0 id)
                               end)
  with
  | Fnil => fun v => v
  | Fcons i t f0 => fun v =>
     if ident_eq id i as b
       return reptype_structlist (if b
                                  then f0
                                  else Fcons i t (all_fields_except_one2 f0 id))
     then
      (if (is_Fnil f0) as b0
         return (if b0 then reptype t else reptype t * reptype_structlist f0) -> reptype_structlist f0
       then fun _ => struct_default_val _
       else fun v => snd v) v
     else
      (if (is_Fnil f0) as b0
         return (if b0 then reptype t else reptype t * reptype_structlist f0) ->
                (if is_Fnil (all_fields_except_one2 f0 id) then reptype t else
                 reptype t * reptype_structlist (all_fields_except_one2 f0 id))
       then fun v =>
         if is_Fnil (all_fields_except_one2 f0 id) as b1
           return if b1 then reptype t else
                  reptype t * reptype_structlist (all_fields_except_one2 f0 id)
         then v
         else (v, struct_default_val _)
       else fun v =>
         if is_Fnil (all_fields_except_one2 f0 id) as b1
           return if b1 then reptype t else
                  reptype t * reptype_structlist (all_fields_except_one2 f0 id)
         then fst v
         else (fst v, proj_except_reptype_structlist f0 id (snd v))
      ) v
  end v
  in
  match f as f'
    return reptype_structlist (match f' with
                               | Fnil => Fnil
                               | Fcons i t f0 =>
                                   if ident_eq id i
                                   then f0
                                   else Fcons i t (all_fields_except_one2 f0 id)
                               end) ->
           reptype_structlist (all_fields_except_one2 f' id)
  with
  | Fnil => fun v => v
  | _ => fun v => v
  end res.

Definition proj_except_reptype_unionlist: reptype_unionlist Fnil := union_default_val _.

Definition proj_except_reptype (t: type) (gf: gfield) (gfs: list gfield) (v: reptype t) : reptype (nf_sub2 t gf gfs) :=
  match gf as GF
    return reptype (nested_field_type2 t gfs) ->
           reptype match GF, nested_field_type2 t gfs with
                   | ArraySubsc i, Tarray t0 n a =>
                     nf_replace2 t gfs (Tstruct 1000%positive
                       (all_fields_except_one2 (ArrayField t0 n a i Tvoid) 1002%positive) noattr)
                   | StructField i, Tstruct i0 f a =>
                     nf_replace2 t gfs (Tstruct i0 (all_fields_except_one2 f i) a)
                   | UnionField i, Tunion i0 f a =>
                     nf_replace2 t gfs (Tunion i0 Fnil a)
                   | _, _ => t
                   end
  with
  | ArraySubsc i =>
    match nested_field_type2 t gfs as T
      return reptype T ->
             reptype match T with
                     | Tarray t0 n a =>
                       nf_replace2 t gfs (Tstruct 1000%positive
                         (all_fields_except_one2 (ArrayField t0 n a i Tvoid) 1002%positive) noattr)
                     | _ => t
                     end
    with
    | Tarray t0 n a =>
      fun v0 => gupd_reptype t gfs
            (Tstruct 1000%positive
              (all_fields_except_one2 (ArrayField t0 n a i Tvoid) 1002%positive) noattr) v
                             (proj_except_reptype_array t0 n a i v0)
    | _ => fun _ => default_val _
    end
  | StructField i  =>
    match nested_field_type2 t gfs as T
      return reptype T ->
             reptype match T with
                     | Tstruct i0 f a =>
                         nf_replace2 t gfs (Tstruct i0 (all_fields_except_one2 f i) a)
                     | _ => t
                     end
    with
    | Tstruct i0 f a => fun v0 => gupd_reptype t gfs (Tstruct i0 (all_fields_except_one2 f i) a) v
                          (proj_except_reptype_structlist f i v0)
    | _ => fun _ => default_val _
    end
  | UnionField i =>
    match nested_field_type2 t gfs as T
      return reptype T ->
             reptype match T with
                     | Tunion i0 f a =>
                         nf_replace2 t gfs (Tunion i0 Fnil a)
                     | _ => t
                     end
    with
    | Tunion i0 f a => fun v0 => gupd_reptype t gfs (Tunion i0 Fnil a) v proj_except_reptype_unionlist
    | _ => fun _ => default_val _
    end
  end (proj_reptype t gfs v).

Definition upd_reptype_array t0 (i: Z) (v: list (reptype t0)) (v0: reptype t0) : list (reptype t0) :=
  (force_lengthn (nat_of_Z i) v (default_val _)) ++ (v0 :: skipn (nat_of_Z (i + 1)) v).

Fixpoint upd_reptype_structlist f (i0: ident) (ofs: Z) (v: reptype_structlist f)
  (v0: reptype match field_offset_rec i0 f ofs, field_type i0 f with
               | Errors.OK _, Errors.OK t0 => t0
               | _, _ => Tvoid
               end) : reptype_structlist f :=
  match f as f'
    return reptype_structlist f' ->
           reptype match field_offset_rec i0 f' ofs, field_type i0 f' with
                   | Errors.OK _, Errors.OK t0 => t0
                   | _, _ => Tvoid
                   end ->
           reptype_structlist f'
  with
  | Fnil => fun _ _ => struct_default_val _
  | Fcons i1 t1 flds0 =>
    if ident_eq i0 i1 as b
      return reptype_structlist (Fcons i1 t1 flds0) ->
             reptype match (if b
                            then Errors.OK (align ofs (alignof t1))
                            else field_offset_rec i0 flds0 (align ofs (alignof t1) + sizeof t1)),
                           (if b then Errors.OK t1 else field_type i0 flds0) with
                     | Errors.OK _, Errors.OK t0 => t0
                     | _, _ => Tvoid
                     end ->
             reptype_structlist (Fcons i1 t1 flds0)
    then if (is_Fnil flds0) as b0
           return (if b0 then reptype t1 else (reptype t1 * reptype_structlist flds0)%type) ->
                  reptype match Errors.OK (align ofs (alignof t1)), Errors.OK t1 with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end ->
                  if b0 then reptype t1 else (reptype t1 * reptype_structlist flds0)%type
         then fun _ v2 => v2
         else fun v1 v2 => (v2, snd v1)
    else if (is_Fnil flds0) as b0
           return (if b0 then reptype t1 else (reptype t1 * reptype_structlist flds0)%type) ->
                  reptype match field_offset_rec i0 flds0 (align ofs (alignof t1) + sizeof t1),
                                field_type i0 flds0 with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end ->
                  if b0 then reptype t1 else (reptype t1 * reptype_structlist flds0)%type
         then fun _ _ => default_val _
         else fun v1 v2 => (fst v1, upd_reptype_structlist flds0 i0 _ (snd v1) v2)
  end v v0.

Fixpoint upd_reptype_unionlist f (i0: ident)
  (v0: reptype match field_type i0 f with
               | Errors.OK t0 => t0
               | _ => Tvoid
               end) : reptype_unionlist f :=
  match f as f'
    return reptype match field_type i0 f' with
                   | Errors.OK t0 => t0
                   | _ => Tvoid
                   end ->
           reptype_unionlist f'
  with
  | Fnil => fun _ => union_default_val _
  | Fcons i1 t1 flds0 =>
    if ident_eq i0 i1 as b
      return reptype match (if b then Errors.OK t1 else field_type i0 flds0) with
                     | Errors.OK t0 => t0
                     | _ => Tvoid
                     end ->
             reptype_unionlist (Fcons i1 t1 flds0)
    then if (is_Fnil flds0) as b0
           return reptype match Errors.OK t1 with
                          | Errors.OK t0 => t0
                          | _ => Tvoid
                          end ->
                  if b0 then reptype t1 else (reptype t1 + reptype_unionlist flds0)%type
         then fun v2 => v2
         else fun v2 => inl v2
    else if (is_Fnil flds0) as b0
           return reptype match field_type i0 flds0 with
                          | Errors.OK t0 => t0
                          | _ => Tvoid
                          end ->
                  if b0 then reptype t1 else (reptype t1 + reptype_unionlist flds0)%type
         then fun _ => default_val _
         else fun v2 => inr (upd_reptype_unionlist flds0 i0 v2)
  end v0.

Fixpoint upd_reptype (t: type) (gfs: list gfield) (v: reptype t) (v0: reptype (nested_field_type2 t gfs)): reptype t :=
  match gfs as gfs'
    return reptype (nested_field_type2 t gfs') -> reptype t
  with
  | nil => fun v1 => v1
  | gf :: gfs0 => fun v1 =>
    let res :=
    match gf as GF
      return reptype (nested_field_type2 t gfs0) ->
             reptype match GF with
                     | ArraySubsc i =>
                       match nested_field_type2 t gfs0 with
                       | Tarray t0 n _ => t0
                       | _ => Tvoid
                       end
                     | StructField i =>
                       match nested_field_type2 t gfs0 with
                       | Tstruct i0 f a =>
                         match field_offset i f, field_type i f with
                         | Errors.OK _, Errors.OK t0 => t0
                         | _, _ => Tvoid
                         end
                       | _ => Tvoid
                       end
                     | UnionField i =>
                       match nested_field_type2 t gfs0 with
                       | Tunion i0 f a =>
                         match field_type i f with
                         | Errors.OK t0 => t0
                         | _ => Tvoid
                         end
                       | _ => Tvoid
                       end
                     end ->
             reptype (nested_field_type2 t gfs0)
    with
    | ArraySubsc i =>
      match nested_field_type2 t gfs0 as T
        return reptype T ->
               reptype (match T with
                        | Tarray t0 n a => t0
                        | _ => Tvoid
                        end) ->
               reptype T
      with
      | Tarray t0 n a => fun v2 v3 => upd_reptype_array t0 i v2 v3
      | _ => fun _ _=> default_val _
      end
    | StructField i =>
      match nested_field_type2 t gfs0 as T
        return reptype T ->
               reptype (match T with
                        | Tstruct i0 f a =>
                          match field_offset i f, field_type i f with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end
                        | _ => Tvoid
                        end) ->
               reptype T
      with
      | Tstruct i0 f a => fun v2 v3 => upd_reptype_structlist f i 0 v2 v3
      | _ => fun _ _ => default_val _
      end
    | UnionField i =>
      match nested_field_type2 t gfs0 as T
        return reptype T ->
               reptype (match T with
                        | Tunion i0 f a =>
                          match field_type i f with
                          | Errors.OK t0 => t0
                          | _ => Tvoid
                          end
                        | _ => Tvoid
                        end) ->
               reptype T
      with
      | Tunion i0 f a => fun _ v3 => upd_reptype_unionlist f i v3
      | _ => fun _ _ => default_val _
      end
    end (proj_reptype t gfs0 v) (eq_rect_r reptype v1 (eq_sym (nested_field_type2_cons _ _ _)))
    in upd_reptype t gfs0 v res
  end v0.

(*
Fixpoint pair_reptype_structlist (id: ident) (f: fieldlist) (ofs: Z)
  (v: reptype_structlist (all_fields_except_one2 f id))
  (v0: reptype match field_offset_rec id f ofs, field_type id f with
               | Errors.OK _, Errors.OK t0 => t0
               | _, _ => Tvoid
               end): reptype_structlist f :=
  match f as f'
    return reptype_structlist (all_fields_except_one2 f' id) ->
           reptype match field_offset_rec id f' ofs, field_type id f' with
                   | Errors.OK _, Errors.OK t0 => t0
                   | _, _ => Tvoid
                   end ->
           reptype_structlist f'
  with
  | Fnil => fun v _ => v
  | Fcons i t flds0 =>
    if ident_eq id i as b
      return reptype_structlist (if b then flds0 else Fcons i t (all_fields_except_one2 flds0 id)) ->
             reptype match (if b
                            then Errors.OK (align ofs (alignof t))
                            else field_offset_rec id flds0 (align ofs (alignof t) + sizeof t)),
                           (if b then Errors.OK t else field_type id flds0)
                     with
                     | Errors.OK _, Errors.OK t0 => t0
                     | _, _ => Tvoid
                     end ->
             if is_Fnil flds0 then reptype t else reptype t * reptype_structlist flds0
    then
      if is_Fnil flds0 as b0
        return reptype_structlist flds0 -> reptype t ->
               (if b0 then reptype t else reptype t * reptype_structlist flds0)
      then fun _ v0 => v0
      else fun v v0 => (v0, v)
    else
      if is_Fnil flds0 as b0
        return (if is_Fnil (all_fields_except_one2 flds0 id)
                then reptype t else reptype t *
                  reptype_structlist (all_fields_except_one2 flds0 id)) ->
               reptype match field_offset_rec id flds0 (align ofs (alignof t) + sizeof t),
                             field_type id flds0 with
                       | Errors.OK _, Errors.OK t0 => t0
                       | _, _ => Tvoid
                       end ->
               (if b0 then reptype t else reptype t * reptype_structlist flds0)
      then
        if is_Fnil (all_fields_except_one2 flds0 id) as b1
          return (if b1 then reptype t else reptype t *
                  reptype_structlist (all_fields_except_one2 flds0 id)) ->
                  reptype match field_offset_rec id flds0 (align ofs (alignof t) + sizeof t),
                             field_type id flds0 with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end -> reptype t
        then fun v v0 => v
        else fun v v0 => fst v
      else
        if is_Fnil (all_fields_except_one2 flds0 id) as b1
          return (if b1 then reptype t else reptype t *
                  reptype_structlist (all_fields_except_one2 flds0 id)) ->
                  reptype match field_offset_rec id flds0 (align ofs (alignof t) + sizeof t),
                             field_type id flds0 with
                          | Errors.OK _, Errors.OK t0 => t0
                          | _, _ => Tvoid
                          end -> reptype t * reptype_structlist flds0
        then fun v v0 => (v, pair_reptype_structlist id flds0 (align ofs (alignof t) + sizeof t)
                             (struct_default_val _) v0)
        else fun v v0 => (fst v, pair_reptype_structlist id flds0 (align ofs (alignof t) + sizeof t)
                                (snd v) v0)
  end v v0.

Lemma pair_reptype_aux: forall t id gfs,
  match nested_field_type2 t gfs with
  | Tstruct i f a => Tstruct i (all_fields_except_one2 f id) a
  | Tunion i f a => Tunion i (all_fields_except_one2 f id) a
  | _ => nested_field_type2 t gfs
  end = nested_field_type2 (nf_sub2 t id gfs) gfs.
Proof.
  intros.
  unfold nf_sub2.
  destruct (nested_field_type2 t gfs) eqn:?; auto.
  + (* Tstruct *)
    apply eq_sym, nested_field_type2_nf_replace2.
    eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto.
  + (* Tunion *)
    apply eq_sym, nested_field_type2_nf_replace2.
    eapply nested_field_type2_Tunion_nested_field_rec_isSome; eauto.
Defined.

Fixpoint pair_reptype (t: type) (id: ident) (gfs: list ident) (v: reptype (nf_sub2 t id gfs)) (v0: reptype (nested_field_type2 t (id :: gfs))) : reptype t :=
  match nested_field_type2 t gfs as T
    return reptype match T with
                   | Tstruct i f a => Tstruct i (all_fields_except_one2 f id) a
                   | Tunion i f a => Tunion i (all_fields_except_one2 f id) a
                   | _ => nested_field_type2 t gfs
                   end ->
           reptype match T with
                   | Tstruct i f a => match field_offset_rec id f 0, field_type id f with
                                      | Errors.OK _, Errors.OK t0 => t0
                                      | _, _ => Tvoid
                                      end
                   | Tunion i f a  => match field_type id f with
                                      | Errors.OK t0 => t0
                                      | _ => Tvoid
                                      end
                   | _ => Tvoid
                   end ->
           t = nf_replace2 (nf_sub2 t id gfs) gfs T ->
           reptype t
  with
  | Tstruct i f a => fun v1 v0 H => eq_rect_r reptype
                       (gupd_reptype _ gfs (Tstruct i f a) v (pair_reptype_structlist id f 0 v1 v0)) H
  | _ => fun _ _ _ => default_val _
  end
  (eq_rect_r reptype (proj_reptype _ gfs v) (pair_reptype_aux t id gfs))
  (eq_rect_r reptype v0 (eq_sym (nested_field_type2_cons t id gfs)))
  (nf_replace2_identical' t id gfs).
*)
Lemma proj_reptype_nil: forall t v, nested_legal_fieldlist t = true -> JMeq (proj_reptype t nil v) v.
Proof.
  intros.
  simpl.
  rewrite eq_rect_r_JMeq.
  reflexivity.
Qed.

Lemma proj_reptype_cons_Tstruct: forall t id gfs i f a v v0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tstruct i f a ->
  JMeq (proj_reptype t gfs v) v0 ->
  JMeq (proj_reptype t (StructField id :: gfs) v) (proj_reptype_structlist id f 0 v0).
Proof.
  intros.
  simpl in *.
  revert H1.
  generalize (proj_reptype t gfs v) as v1.
  generalize (nested_field_type2_cons t (StructField id) gfs) as HH.
  rewrite H0.
  intros; clear v.
  rewrite eq_rect_r_JMeq.
  rewrite H1.
  reflexivity.
Qed.

(*
Module Test.
  Definition T1 := Tstruct 1%positive (Fcons 101%positive tint (Fcons 102%positive tint Fnil)) noattr.
  Definition T2 := Tstruct 2%positive (Fcons 201%positive T1 (Fcons 202%positive T1 Fnil)) noattr.
  Definition T3 := Tstruct 3%positive (Fcons 301%positive T2 (Fcons 302%positive T2 Fnil)) noattr.

  Definition v : reptype T3 :=
   (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))),
    ((Vint (Int.repr 5), Vint (Int.repr 6)), (Vint (Int.repr 7), Vint (Int.repr 8)))).

  Arguments eq_rect_r / {A} {x} P H {y} H0.
  Arguments proj_except_reptype / t gf gfs v.

  Lemma Test1:
    JMeq (proj_reptype T3 (StructField 201%positive :: StructField 302%positive :: nil) v) (Vint (Int.repr 5), Vint (Int.repr 6)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma Test2:
    JMeq (upd_reptype T3 (StructField 201%positive :: StructField 302%positive :: nil) v
    (Vint (Int.repr 15), Vint (Int.repr 16)))
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))),
    ((Vint (Int.repr 15), Vint (Int.repr 16)), (Vint (Int.repr 7), Vint (Int.repr 8)))).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma Test3:
    JMeq (proj_except_reptype T3 (StructField 201%positive) (StructField 302%positive :: nil) v)
    (((Vint (Int.repr 1), Vint (Int.repr 2)), (Vint (Int.repr 3), Vint (Int.repr 4))),
    ((Vint (Int.repr 7), Vint (Int.repr 8)))).
  Proof.
    simpl.
    reflexivity.
  Qed.
End Test.
*)

Lemma upd_reptype_nil: forall t v v0, upd_reptype t nil v v0 = v0.
Proof.
  intros.
  reflexivity.
Qed.

Lemma upd_reptype_cons: forall t gf gfs v v0 v0',
  legal_nested_field t (gf :: gfs) ->
  JMeq v0 v0' ->
  upd_reptype t (gf :: gfs) v v0 =
    upd_reptype t gfs v (upd_reptype _ (gf :: nil) (proj_reptype t gfs v) v0').
Proof.
  intros.
  simpl.
  f_equal.
  generalize (nested_field_type2_cons t gf gfs).
  generalize (nested_field_type2_nil (nested_field_type2 t gfs)).
  generalize (eq_sym (nested_field_type2_cons (nested_field_type2 t gfs) gf nil)).
  generalize (proj_reptype t gfs v).
  revert v0' H0.
  solve_legal_nested_field_cons H.
Opaque reptype.
  + simpl.
    simpl.
Transparent reptype.
    intros.
    f_equal.
    - apply JMeq_eq.
      rewrite eq_rect_r_JMeq.
      reflexivity.
    - apply JMeq_eq.
      rewrite !eq_rect_r_JMeq.
      rewrite H2.
      reflexivity.
Opaque reptype.
  + simpl.
Transparent reptype.
    intros.
    f_equal.
    - apply JMeq_eq.
      rewrite eq_rect_r_JMeq.
      reflexivity.
    - apply JMeq_eq.
      rewrite !eq_rect_r_JMeq.
      rewrite H2.
      reflexivity.
Opaque reptype.
  + simpl.
Transparent reptype.
    intros.
    f_equal.
    - apply JMeq_eq.
      rewrite !eq_rect_r_JMeq.
      rewrite H2.
      reflexivity.
Qed.

Definition gupd_reptype_array_is_pair: forall t n a i t0,
  0 <= i < n ->
  sigT (fun F => sigT (fun G =>
    forall v v0,
      F (gupd_reptype_array t n a i t0 v v0) =
        (proj_except_reptype_array t n a i v, v0) /\
      gupd_reptype_array t n a i t0 v v0 =
        G (proj_except_reptype_array t n a i v, v0)
  )).
Proof.
  intros.
  unfold gupd_reptype_array, proj_except_reptype_array, ArrayField.
  destruct (i =? 0) eqn:?H; [| destruct (i =? n - 1) eqn:?H].
  + exists (fun v => (snd v, fst v)).
    exists (fun v => (snd v, fst v)).
    intros.
    split; reflexivity.
  + exists (fun v => v).
    exists (fun v => v).
    intros.
    split; reflexivity.
  + exists (fun v => ((fst v, snd (snd v)), (fst (snd v)))).
    exists (fun v => (fst (fst v), (snd v, snd (fst v)))).
    intros.
    split; reflexivity.
Defined.

Definition gupd_reptype_structlist_is_pair: forall f i t0,
  isOK (field_type i f) = true ->
  sigT (fun F => sigT (fun G =>
    forall v v0,
      F (gupd_reptype_structlist f i t0 v v0) =
        (proj_except_reptype_structlist f i v, v0) /\
      gupd_reptype_structlist f i t0 v v0 =
        G (proj_except_reptype_structlist f i v, v0)
  )).
Proof.
  intros.
  induction f.
  + inversion H.
  + simpl in H |- *.
    if_tac in H.
    - unfold eq_rect_r, eq_rect; simpl.
      if_tac.
      * exists (fun v => (struct_default_val f, v)).
        exists (fun v => snd v).
        intros.
        split; reflexivity.
      * exists (fun v => (snd v, fst v)).
        exists (fun v => (snd v, fst v)).
        intros.
        split; reflexivity.
    - unfold eq_rect_r, eq_rect; simpl.
      destruct (is_Fnil f) eqn:?H;
        [destruct f; [inversion H | inversion H1] |].
      pose proof is_Fnil_all_fields_replace_one2 f i t0.
      rewrite H1 in H2.
      rewrite H2.
      specialize (IHf H).
      destruct (is_Fnil (all_fields_except_one2 f i)) eqn:?H.
      * destruct IHf as [F0 [G0 ?H]].
        exists (fun v => (fst v, snd (F0 (snd v)))).
        exists (fun v => (fst v, G0 (struct_default_val _, snd v))).
        intros.
        assert (proj_except_reptype_structlist f i (snd v) =
          struct_default_val (all_fields_except_one2 f i)).
        {
          match goal with
          | |- ?A = ?B => generalize A B; intros
          end.
          clear - H3.
          destruct (all_fields_except_one2 f i); [| inversion H3].
          simpl in *; destruct r, r0; reflexivity.
        }
        destruct (H4 (snd v) v0).
        rewrite H5 in H6, H7.
        simpl; rewrite H6, <- H7.
        split; reflexivity.
      * destruct IHf as [F0 [G0 ?H]].
        exists (fun v => (fst v, fst (F0 (snd v)), snd (F0 (snd v)))).
        exists (fun v => (fst (fst v), G0 (snd (fst v), snd v))).
        intros.
        destruct (H4 (snd v) v0).
        simpl; rewrite H5, <- H6.
        split; reflexivity.
Defined.

Definition gupd_reptype_unionlist_is_pair: forall f i t0,
  sigT (fun F => sigT (fun G =>
    forall (v: reptype_unionlist f) v0,
      F (gupd_reptype_unionlist i t0 v0) = (proj_except_reptype_unionlist, v0) /\
      gupd_reptype_unionlist i t0 v0 = G (proj_except_reptype_unionlist, v0))).
Proof.
  intros.
  unfold gupd_reptype_unionlist, proj_except_reptype_unionlist.
  simpl.
  exists (fun v => (tt, v)).
  exists (fun v => snd v).
  intros.
  split; reflexivity.
Defined.

Lemma nf_sub2_is_nf_sub2_1_nf_replace2: forall t gf gfs,
  legal_nested_field t (gf :: gfs) ->
  nf_replace2 t gfs (nf_sub2 (nested_field_type2 t gfs) gf nil) = nf_sub2 t gf gfs.
Proof.
  intros.
  unfold nf_sub2.
  solve_legal_nested_field_cons H.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

Lemma nf_replace2_is_nf_replace2_1_nf_replace2: forall t gf gfs t0,
  legal_nested_field t (gf :: gfs) ->
  nf_replace2 t gfs (nf_replace2 (nested_field_type2 t gfs) (gf :: nil) t0) =
  nf_replace2 t (gf :: gfs) t0.
Proof.
  intros.
  unfold nf_replace2 at 2 3.
  solve_legal_nested_field_cons H.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

Lemma proj_except_reptype_is_proj_except_reptye1_gupd_reptype: forall t gf gfs v,
  legal_nested_field t (gf :: gfs) ->
  JMeq (proj_except_reptype t gf gfs v)
    (gupd_reptype t gfs _ v
      (proj_except_reptype _ gf nil (proj_reptype t gfs v))).
Proof.
  intros.
  apply legal_nested_field_cons_lemma in H.
  destruct H.
  unfold proj_except_reptype, nf_sub2.
  generalize (proj_reptype t gfs v).
  destruct gf, (nested_field_type2 t gfs) eqn:?H; try solve [inversion H0]; intro proj_v.
  + simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    reflexivity.
  + simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    reflexivity.
  + simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    reflexivity.
Qed.

Lemma gupd_reptype_is_gupd_reptye1_gupd_reptype: forall t gf gfs t0 v v0,
  legal_nested_field t (gf :: gfs) ->
  JMeq (gupd_reptype t (gf :: gfs) t0 v v0)
    (gupd_reptype t gfs _ v
      (gupd_reptype _ (gf :: nil) _ (proj_reptype t gfs v) v0)).
Proof.
  intros.
  apply legal_nested_field_cons_lemma in H.
  destruct H.
  simpl.
  generalize (proj_reptype t gfs v).
  destruct gf, (nested_field_type2 t gfs) eqn:?H; try solve [inversion H0]; intro proj_v.
  + simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    reflexivity.
  + simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    reflexivity.
  + simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    reflexivity.
Qed.

Definition gupd_reptype1_is_pair: forall t gf t0,
  legal_nested_field t (gf :: nil) ->
  sigT (fun F => sigT (fun G =>
    forall v v0,
      F (gupd_reptype t (gf :: nil) t0 v v0) = (proj_except_reptype t gf nil v, v0) /\
      gupd_reptype t (gf :: nil) t0 v v0 = G (proj_except_reptype t gf nil v, v0))).
Proof.
  intros.
  solve_legal_nested_field_cons H; simpl;
  change (nested_field_type2 t nil) with t in Heq0 |- *;
  subst.
  + unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    apply gupd_reptype_array_is_pair; auto.
  + unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    apply gupd_reptype_structlist_is_pair; auto.
  + unfold eq_rect_r, eq_rect, nested_field_type2_nil.
    simpl.
    apply gupd_reptype_unionlist_is_pair.
Defined.

Definition gupd_reptype_cons_is_pair: forall t gf gfs t0,
  legal_nested_field t (gf :: gfs) ->
  sigT (fun F => sigT (fun G =>
    forall v v0,
      F (gupd_reptype t (gf :: gfs) t0 v v0) = (proj_except_reptype t gf gfs v, v0) /\
      gupd_reptype t (gf :: gfs) t0 v v0 = G (proj_except_reptype t gf gfs v, v0))).
Proof.
  intros.
  revert gf t0 H; induction gfs; intros.
  + apply gupd_reptype1_is_pair; auto.
  + remember (a :: gfs) as gfs'.
    cut (sigT (fun F => sigT (fun G =>
          forall (v : reptype t) (v0 : reptype t0),
          F (gupd_reptype t gfs' _ v
              (gupd_reptype _ (gf :: nil) t0 (proj_reptype t gfs' v) v0)) =
          (gupd_reptype t gfs' _ v
            (proj_except_reptype _ gf nil (proj_reptype t gfs' v)), v0) /\
          gupd_reptype t gfs' _ v
              (gupd_reptype _ (gf :: nil) t0 (proj_reptype t gfs' v) v0) =
          G (gupd_reptype t gfs' _ v
              (proj_except_reptype _ gf nil (proj_reptype t gfs' v)), v0)))).
    {
      intros ?H.
      destruct H0 as [F0 [G0 ?H]].
      exists (fun v =>
             let r := F0 (eq_rect_r reptype v
               (nf_replace2_is_nf_replace2_1_nf_replace2 t gf gfs' t0 H))
             in
             (eq_rect_r reptype (fst r)
               (eq_sym (nf_sub2_is_nf_sub2_1_nf_replace2 t gf gfs' H)), snd r))
             .
      exists (fun v =>
             let l := G0 (eq_rect_r reptype (fst v)
               (nf_sub2_is_nf_sub2_1_nf_replace2 t gf gfs' H), snd v)
             in
             eq_rect_r reptype l
               (eq_sym (nf_replace2_is_nf_replace2_1_nf_replace2 t gf gfs' t0 H)))
             .
      intros.
      replace (proj_except_reptype t gf gfs' v) with
        (eq_rect_r reptype
          (gupd_reptype t gfs' (nf_sub2 (nested_field_type2 t gfs') gf nil) v
            (proj_except_reptype (nested_field_type2 t gfs') gf nil
            (proj_reptype t gfs' v)))
          (eq_sym (nf_sub2_is_nf_sub2_1_nf_replace2 t gf gfs' H))).
      2:{
        apply JMeq_eq.
        eapply JMeq_trans; [apply eq_rect_r_JMeq |].
        apply JMeq_sym, proj_except_reptype_is_proj_except_reptye1_gupd_reptype; auto.
      }
      replace (gupd_reptype t (gf :: gfs') t0 v v0) with
        (eq_rect_r reptype
          (gupd_reptype t gfs'
            (nf_replace2 (nested_field_type2 t gfs') (gf :: nil) t0) v
            (gupd_reptype (nested_field_type2 t gfs')
               (gf :: nil) t0 (proj_reptype t gfs' v) v0))
          (eq_sym (nf_replace2_is_nf_replace2_1_nf_replace2 t gf gfs' t0 H))).
      2:{
        apply JMeq_eq.
        eapply JMeq_trans; [apply eq_rect_r_JMeq |].
        apply JMeq_sym, gupd_reptype_is_gupd_reptye1_gupd_reptype; auto.
      }
      unfold fst at 2.
      unfold snd at 2.
      rewrite !eq_rect_r_eq_rect_r_eq_sym'.
      specialize (H0 v v0).
      destruct H0.
      split.
      + rewrite H0.
        reflexivity.
      + rewrite H1.
        reflexivity.
    }
    pose proof (IHgfs a (nf_replace2 (nested_field_type2 t gfs') (gf :: nil) t0)) as HH0.
    spec HH0; [subst gfs'; solve_legal_nested_field_cons H; auto|].
    pose proof (IHgfs a (nf_sub2 (nested_field_type2 t gfs') gf nil)) as HH1.
    spec HH1; [subst gfs'; solve_legal_nested_field_cons H; auto|].
    destruct HH0 as [F0 [G0 ?H]].
    destruct HH1 as [F1 [G1 ?H]].
    destruct (gupd_reptype1_is_pair (nested_field_type2 t gfs') gf t0) as [F2 [G2 ?H]].
    {
      apply legal_nested_field_app'. auto.
    }
    subst gfs'.
    exists (fun v =>
              let r1 := F0 v in
              let r2 := F2 (snd r1) in
              let r3 := G1 (fst r1, fst r2) in
              (r3, snd r2)).
    exists (fun v =>
              let r1 := F1 (fst v) in
              let r2 := G2 (snd r1, snd v) in
              let r3 := G0 (fst r1, r2) in
              r3).
    intros.
Opaque gupd_reptype proj_except_reptype nested_field_type2 nf_replace2 nf_sub2 proj_reptype.
    simpl. (* Pretty slow *)
Transparent gupd_reptype proj_except_reptype nested_field_type2 nf_replace2 nf_sub2 proj_reptype.
    rewrite !(proj1 (H0 _ _)).
    unfold fst at 3; rewrite !(proj1 (H1 _ _)).
    unfold snd at 1 3; rewrite !(proj1 (H2 _ _)).
    unfold snd at 2; rewrite <- !(proj2 (H2 _ _)).
    unfold fst at 1; rewrite <- (proj2 (H1 _ _)).
    rewrite <- (proj2 (H0 _ _)).
    split; reflexivity.
Qed.

Definition proj_except_reptype_cons_is_pair: forall t gf gf0 gfs,
  legal_nested_field t (gf :: gf0 :: gfs) ->
  sigT (fun F => sigT (fun G =>
    forall v,
    F (proj_except_reptype t gf (gf0 :: gfs) v) =
      (proj_except_reptype t gf0 gfs v,
        proj_except_reptype _ gf nil (proj_reptype t (gf0 :: gfs) v)) /\
    proj_except_reptype t gf (gf0 :: gfs) v =
      G (proj_except_reptype t gf0 gfs v,
        proj_except_reptype _ gf nil (proj_reptype t (gf0 :: gfs) v)))).
Proof.
  intros.
  cut (sigT (fun F => sigT (fun G =>
         forall v,
         F (gupd_reptype t (gf0 :: gfs) _ v
             (proj_except_reptype _ gf nil (proj_reptype t (gf0 :: gfs) v))) =
           (proj_except_reptype t gf0 gfs v,
             proj_except_reptype _ gf nil (proj_reptype t (gf0 :: gfs) v)) /\
         gupd_reptype t (gf0 :: gfs) _ v
             (proj_except_reptype _ gf nil (proj_reptype t (gf0 :: gfs) v)) =
           G (proj_except_reptype t gf0 gfs v,
             proj_except_reptype _ gf nil (proj_reptype t (gf0 :: gfs) v))))).
  {
    intros ?H.
    destruct H0 as [F0 [G0 ?H]].
    exists (fun v => F0 (eq_rect_r reptype v
             (nf_sub2_is_nf_sub2_1_nf_replace2 t gf (gf0 :: gfs) H))).
    exists (fun v => eq_rect_r reptype (G0 v)
             (eq_sym (nf_sub2_is_nf_sub2_1_nf_replace2 t gf (gf0 :: gfs) H))).
    intros.
    split.
    + rewrite <- (proj1 (H0 _)).
      f_equal.
      apply JMeq_eq.
      eapply JMeq_trans; [apply eq_rect_r_JMeq |].
      apply proj_except_reptype_is_proj_except_reptye1_gupd_reptype.
      auto.
    + rewrite <- (proj2 (H0 _)).
      apply JMeq_eq, JMeq_sym.
      eapply JMeq_trans; [apply eq_rect_r_JMeq |].
      apply JMeq_sym, proj_except_reptype_is_proj_except_reptye1_gupd_reptype.
      auto.
  }
  destruct (gupd_reptype_cons_is_pair t gf0 gfs
             (nf_sub2 (nested_field_type2 t (gf0 :: gfs)) gf nil)) as [F0 [G0 ?H]];
    [solve_legal_nested_field_cons H; auto |].
  exists F0, G0.
  intros.
  apply H0.
Defined.
