Require Import VST.veric.Clight_base.
Require Export compcert.lib.Axioms.
Require Import compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Floats.
Require Export compcert.lib.Maps.
Require Export compcert.common.AST.
Require Export compcert.common.Values.
Require Export compcert.cfrontend.Ctypes.
Require Export compcert.cfrontend.Clight.
Require Export VST.sepcomp.Address.
Require Export VST.msl.eq_dec.
Require Export VST.msl.shares.
Require Export VST.msl.predicates_rec.
Require Export VST.msl.contractive.
Require Export VST.msl.seplog.
Require Export VST.msl.ghost_seplog.
Require Export VST.msl.alg_seplog.
Require Export VST.msl.log_normalize.
Require Export VST.msl.wand_frame.
Require Export VST.msl.wandQ_frame.
Require Export VST.msl.ramification_lemmas.
Require Export VST.veric.tycontext.
Require Export VST.veric.change_compspecs.
Require Export VST.veric.mpred.
Require Export VST.veric.expr.
Require Export VST.veric.expr_rel.
Require Export VST.veric.Clight_lemmas.
Require Export VST.veric.composite_compute.
Require Export VST.veric.align_mem.
Require Export VST.veric.shares.
(*exported by Clight_seplog: Require VST.veric.seplog.*)
Require VST.veric.Clight_seplog.
Require VST.veric.Clight_assert_lemmas.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.valid_pointer.
Require Import VST.veric.own.
Require VST.veric.semax_prog.
Require VST.veric.semax_ext.

Instance Nveric: NatDed mpred := algNatDed compcert_rmaps.RML.R.rmap.
Instance Sveric: SepLog mpred := algSepLog compcert_rmaps.RML.R.rmap.
Instance Cveric: ClassicalSep mpred := algClassicalSep compcert_rmaps.RML.R.rmap.
Instance Iveric: Indir mpred := algIndir compcert_rmaps.RML.R.rmap.
Instance Rveric: RecIndir mpred := algRecIndir compcert_rmaps.RML.R.rmap.
Instance SIveric: SepIndir mpred := algSepIndir compcert_rmaps.RML.R.rmap.
Instance CSLveric: CorableSepLog mpred := algCorableSepLog compcert_rmaps.RML.R.rmap.
Instance CIveric: CorableIndir mpred := algCorableIndir compcert_rmaps.RML.R.rmap.
Instance SRveric: SepRec mpred := algSepRec compcert_rmaps.RML.R.rmap.
Instance Bveric: BupdSepLog mpred gname compcert_rmaps.RML.R.preds :=
  mkBSL _ _ _ _ _ bupd (@own) bupd_intro bupd_mono bupd_trans bupd_frame_r
    (@ghost_alloc) (@ghost_op) (@ghost_valid_2) (@ghost_update_ND) (@ghost_dealloc).

Instance LiftNatDed' T {ND: NatDed T}: NatDed (LiftEnviron T) := LiftNatDed _ _.
Instance LiftSepLog' T {ND: NatDed T}{SL: SepLog T}: SepLog (LiftEnviron T) := LiftSepLog _ _.
Instance LiftClassicalSep' T {ND: NatDed T}{SL: SepLog T}{CS: ClassicalSep T} :
           ClassicalSep (LiftEnviron T) := LiftClassicalSep _ _.
Instance LiftIndir' T {ND: NatDed T}{SL: SepLog T}{IT: Indir T} :
           Indir (LiftEnviron T) := LiftIndir _ _.
Instance LiftSepIndir' T {ND: NatDed T}{SL: SepLog T}{IT: Indir T}{SI: SepIndir T} :
           SepIndir (LiftEnviron T) := LiftSepIndir _ _.
Instance LiftCorableSepLog' T {ND: NatDed T}{SL: SepLog T}{CSL: CorableSepLog T} :
           CorableSepLog (LiftEnviron T) := LiftCorableSepLog _ _.
Instance LiftCorableIndir' T {ND: NatDed T}{SL: SepLog T}{IT: Indir T}{SI: SepIndir T}{CSL: CorableSepLog T}{CI: CorableIndir T} :
           CorableIndir (LiftEnviron T) := LiftCorableIndir _ _.

Definition local:  (environ -> Prop) -> environ->mpred :=  lift1 prop.

Global Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric CSLveric CIveric SRveric Bveric.

Hint Resolve any_environ : typeclass_instances.

Local Open Scope logic.

Transparent mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric CSLveric CIveric SRveric Bveric.

(* BEGIN from expr2.v *)
Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => prop (is_true (Int.eq i Int.zero))
         | Vlong i => prop (is_true (Int64.eq i Int64.zero))
         | _ => FF
         end.

Definition denote_tc_nonzero v : mpred :=
         match v with
         | Vint i => prop (i <> Int.zero)
         | Vlong i =>prop (i <> Int64.zero)
         | _ => FF end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => prop (Int.unsigned i1 < Int.unsigned i)
     | _ => FF
     end.

Definition denote_tc_lgt l v : mpred :=
     match v with
     | Vlong l1 => prop (Int64.unsigned l1 < Int64.unsigned l)
     | _ => FF
     end.

Definition Zoffloat (f:float): option Z := (**r conversion to Z *)
  match f with
    | Fappli_IEEE.B754_finite s m (Zpos e) _ =>
       Some (Fcore_Zaux.cond_Zopp s (Zpos m) * Zpower_pos 2 e)%Z
    | Fappli_IEEE.B754_finite s m 0 _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m))
    | Fappli_IEEE.B754_finite s m (Zneg e) _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m / Zpower_pos 2 e))
    | Fappli_IEEE.B754_zero _ => Some 0
    | _ => None
  end.  (* copied from CompCert 2.3, because it's missing in CompCert 2.4 *)

Definition Zofsingle (f: float32): option Z := (**r conversion to Z *)
  match f with
    | Fappli_IEEE.B754_finite s m (Zpos e) _ =>
       Some (Fcore_Zaux.cond_Zopp s (Zpos m) * Zpower_pos 2 e)%Z
    | Fappli_IEEE.B754_finite s m 0 _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m))
    | Fappli_IEEE.B754_finite s m (Zneg e) _ => Some (Fcore_Zaux.cond_Zopp s (Zpos m / Zpower_pos 2 e))
    | Fappli_IEEE.B754_zero _ => Some 0
    | _ => None
  end.  (* copied from CompCert 2.3, because it's missing in CompCert 2.4 *)


Definition denote_tc_Zge z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition denote_tc_Zle z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition sameblock v1 v2 : bool :=
         match v1, v2 with
          | Vptr b1 _, Vptr b2 _ => peq b1 b2
          | _, _ => false
         end.

Definition denote_tc_samebase v1 v2 : mpred :=
       prop (is_true (sameblock v1 v2)).

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => prop (~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone))
          | Vlong n1, Vlong n2 => prop (~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone))
          | Vint n1, Vlong n2 => TT
          | Vlong n1, Vint n2 => prop (~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone))
          | _ , _ => FF
        end.

Definition denote_tc_nosignedover (op: Z->Z->Z) v1 v2 : mpred :=
 match v1,v2 with
 | Vint n1, Vint n2 => 
   prop (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed)
 | Vlong n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vint n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vlong n1, Vint n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int.signed n2) <= Int64.max_signed)
 | _, _ => FF
 end.

Definition denote_tc_initialized id ty rho : mpred :=
    prop (exists v, Map.get (te_of rho) id = Some v
               /\ tc_val ty v).

Definition denote_tc_isptr v : mpred :=
  prop (isptr v).

Definition test_eq_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else (andp (valid_pointer v1) (valid_pointer v2)).

Definition test_order_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else FF.

Definition denote_tc_test_eq v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => 
     if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => 
     if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vint i, Vptr _ _ =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v2)
 | Vlong i, Vptr _ _ =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v2) else FF
 | Vptr _ _, Vint i =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v1)
 | Vptr _ _, Vlong i =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v1) else FF
 | Vptr _ _, Vptr _ _ =>
      test_eq_ptrs v1 v2
 | _, _ => FF
 end.

Definition denote_tc_test_order v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vptr _ _, Vptr _ _ =>
      test_order_ptrs v1 v2
 | _, _ => FF
 end.

Definition typecheck_error (e: tc_error) : Prop := False.
Global Opaque typecheck_error.

(* Somehow, this fixes a universe collapse issue that will occur if fool is not defined. *)
Definition fool := @map _ Type (fun it : ident * type => mpred).

Fixpoint denote_tc_assert {CS: compspecs} (a: tc_assert) : environ -> mpred :=
  match a with
  | tc_FF msg => `(prop (typecheck_error msg))
  | tc_TT => TT
  | tc_andp' b c => fun rho => andp (denote_tc_assert b rho) (denote_tc_assert c rho)
  | tc_orp' b c => `orp (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr e)
  | tc_isptr e => `denote_tc_isptr (eval_expr e)
  | tc_test_eq' e1 e2 => `denote_tc_test_eq (eval_expr e1) (eval_expr e2)
  | tc_test_order' e1 e2 => `denote_tc_test_order (eval_expr e1) (eval_expr e2)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr e)
  | tc_llt' e i => `(denote_tc_lgt i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr e)
  | tc_nosignedover op e1 e2 => `(denote_tc_nosignedover op) (eval_expr e1) (eval_expr e2)
 end.

Definition fool' := @map _ Type (fun it : ident * type => mpred).

Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric CSLveric CIveric SRveric Bveric.

(* END from expr2.v *)

Definition cast_pointer_to_bool t1 t2 :=
 match t1 with (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => 
           match t2 with Tint IBool _ _ => true | _ => false end
 | _ => false
end.

Fixpoint ext_link_prog' (dl: list (ident * globdef fundef type)) (s: String.string) : option ident :=
 match dl with
 | (id, Gfun (External EF_malloc _ _ _)) :: dl' =>
      if String.string_dec s "_malloc" then Some id else ext_link_prog' dl' s
 | (id, Gfun (External EF_free _ _ _)) :: dl' =>
      if String.string_dec s "_free" then Some id else ext_link_prog' dl' s
 | (id, Gfun (External (EF_external s' _) _ _ _)) :: dl' =>
      if String.string_dec s s' then Some id else ext_link_prog' dl' s
 | (id, Gfun (External (EF_builtin s' _) _ _ _)) :: dl' =>
      if String.string_dec s s' then Some id else ext_link_prog' dl' s
 | _ :: dl' =>
     ext_link_prog' dl' s
 | nil => None
 end.

Definition ext_link_prog (p: program) (s: String.string) : ident :=
  match ext_link_prog' (prog_defs p) s with Some id => id | None => 1%positive end.

Definition closed_wrt_vars {B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho te',
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition closed_wrt_lvars {B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho ve',
     (forall i, S i \/ Map.get (ve_of rho) i = Map.get ve' i) ->
     F rho = F (mkEnviron (ge_of rho) ve' (te_of rho)).

Definition not_a_param (params: list (ident * type)) (i : ident) : Prop :=
  ~ In i (map (@fst _ _) params).

Definition is_a_local (vars: list (ident * type)) (i: ident) : Prop :=
  In  i (map (@fst _ _) vars) .

Definition precondition_closed (f: function) {A: rmaps.TypeTree}
  (P: forall ts, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred) : Prop :=
 forall ts x,
  closed_wrt_vars (not_a_param (fn_params f)) (P ts x) /\
  closed_wrt_lvars (is_a_local (fn_vars f)) (P ts x).

Definition typed_true (t: type) (v: val)  : Prop :=  strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop :=  strict_bool_val v t =
Some false.

Definition subst {A} (x: ident) (v: environ -> val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x (v s)).

Definition substopt {A} (ret: option ident) (v: environ -> val) (P: environ -> A)  : environ -> A :=
   match ret with
   | Some id => subst id v P
   | None => P
   end.

Definition cast_expropt {CS: compspecs} (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr (Ecast e' t))  | None => `None end.

Definition typecheck_tid_ptr_compare
Delta id :=
match (temp_types Delta) ! id with
| Some t => is_int_type t
| None => false
end.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch =>
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs =>
       if readable_share_dec sh
       then (!!tc_val t v2 &&
             res_predicates.address_mapsto ch v2 sh (b, Ptrofs.unsigned ofs)) ||
            (!! (v2 = Vundef) &&
             EX v2':val, res_predicates.address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))
       else !! (tc_val' t v2 /\ (Memdata.align_chunk ch | Ptrofs.unsigned ofs)) && res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (Memdata.size_chunk ch)
     | _ => FF
    end
    | _ => FF
    end
  | _ => FF
  end.

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Definition mapsto_zeros (n: Z) (sh: share) (a: val) : mpred :=
 match a with
  | Vptr b z => 
    !! (0 <= Ptrofs.unsigned z  /\ n + Ptrofs.unsigned z < Ptrofs.modulus)%Z &&
    mapsto_memory_block.address_mapsto_zeros sh (nat_of_Z n) (b, Ptrofs.unsigned z)
  | _ => FF
  end.

Definition init_data2pred (d: init_data)  (sh: share) (a: val) (rho: environ) : mpred :=
 match d with
  | Init_int8 i => mapsto sh (Tint I8 Unsigned noattr) a (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh (Tint I16 Unsigned noattr) a (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh (Tint I32 Unsigned noattr) a (Vint i)
  | Init_int64 i => mapsto sh (Tlong Unsigned noattr) a (Vlong i)
  | Init_float32 r =>  mapsto sh (Tfloat F32 noattr) a (Vsingle r)
  | Init_float64 r =>  mapsto sh (Tfloat F64 noattr) a (Vfloat r)
  | Init_space n => mapsto_zeros n sh a
  | Init_addrof symb ofs =>
       match Map.get (ge_of rho) symb with
       | Some b => mapsto sh (Tpointer Tvoid noattr) a (Vptr b ofs)
       | _ => mapsto_ sh (Tpointer Tvoid noattr) a
       end
 end.

(*Definition extern_retainer : share := fst (Share.split Share.Lsh). *)

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | Init_space n => Z.max n 0
  end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Fixpoint init_data_list2pred  (dl: list init_data)
                           (sh: share) (v: val)  : environ -> mpred :=
  match dl with
  | d::dl' => 
      sepcon (init_data2pred d sh v) 
                  (init_data_list2pred dl' sh (offset_val (init_data_size d) v))
  | nil => emp
 end.

Definition readonly2share (rdonly: bool) : share :=
  if rdonly then Ers else Ews.

Definition globals := ident -> val.

Definition globvar2pred (gv: globals) (idv: ident * globvar type) : environ->mpred :=
   if (gvar_volatile (snd idv))
                       then  lift0 TT
                       else    init_data_list2pred (gvar_init (snd idv))
                                   (readonly2share (gvar_readonly (snd idv))) (gv (fst idv)).

Definition globals_of_env (rho: environ) (i: ident) : val := 
  match Map.get (ge_of rho) i with Some b => Vptr b Ptrofs.zero | None => Vundef end.

Definition globvars2pred  (gv: globals)  (vl: list (ident * globvar type)) : environ->mpred :=
  (lift2 andp) (fun rho => prop (gv = globals_of_env rho))
  (fold_right sepcon emp (map (globvar2pred gv) vl)).

Definition initializer_aligned (z: Z) (d: init_data) : bool :=
  match d with
  | Init_int16 n => Zeq_bool (z mod 2) 0
  | Init_int32 n => Zeq_bool (z mod 4) 0
  | Init_int64 n => Zeq_bool (z mod 8) 0
  | Init_float32 n =>  Zeq_bool (z mod 4) 0
  | Init_float64 n =>  Zeq_bool (z mod 8) 0
  | Init_addrof symb ofs =>  Zeq_bool (z mod (size_chunk Mptr)) 0
  | _ => true
  end.

Fixpoint initializers_aligned (z: Z) (dl: list init_data) : bool :=
  match dl with
  | nil => true
  | d::dl' => andb (initializer_aligned z d) (initializers_aligned (z + init_data_size d) dl')
  end.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with
 | Vptr b ofs => (!! (Ptrofs.unsigned ofs + n < Ptrofs.modulus)) && mapsto_memory_block.memory_block' sh (nat_of_Z n) b (Ptrofs.unsigned ofs)
 | _ => FF
 end.

Lemma memory_block_zero_Vptr: forall sh b z, memory_block sh 0 (Vptr b z) = emp.
Proof. exact mapsto_memory_block.memory_block_zero_Vptr. Qed.

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' |-- mapsto_ sh t v.
Proof. exact mapsto_memory_block.mapsto_mapsto_. Qed.

Lemma mapsto_tc_val': forall sh t p v, mapsto sh t p v |-- !! tc_val' t v.
Proof. exact mapsto_memory_block.mapsto_tc_val'. Qed.

Lemma memory_block_split:
  forall (sh : share) (b : block) (ofs n m : Z),
  0 <= n ->
  0 <= m ->
  n + m <= n + m + ofs < Ptrofs.modulus ->
  memory_block sh (n + m) (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh n (Vptr b (Ptrofs.repr ofs)) *
  memory_block sh m (Vptr b (Ptrofs.repr (ofs + n))).
Proof. exact mapsto_memory_block.memory_block_split. Qed.

Lemma mapsto_share_join:
 forall sh1 sh2 sh t p v,
   sepalg.join sh1 sh2 sh ->
   mapsto sh1 t p v * mapsto sh2 t p v = mapsto sh t p v.
Proof.
intros.
apply  mapsto_memory_block.mapsto_share_join; auto.
Qed.

Lemma memory_block_share_join:
  forall sh1 sh2 sh n p,
   sepalg.join sh1 sh2 sh ->
   memory_block sh1 n p * memory_block sh2 n p = memory_block sh n p.
Proof.
intros.
apply  mapsto_memory_block.memory_block_share_join; auto.
Qed.

Lemma mapsto_conflict:
  forall sh t v v2 v3,
  sepalg.nonunit sh ->
  mapsto sh t v v2 * mapsto sh t v v3 |-- FF.
Proof.
intros.
apply mapsto_memory_block.mapsto_conflict; auto.
Qed.

Lemma memory_block_conflict: forall sh n m p,
  sepalg.nonunit sh ->
  0 < n <= Ptrofs.max_unsigned -> 0 < m <= Ptrofs.max_unsigned ->
  memory_block sh n p * memory_block sh m p |-- FF.
Proof.
intros.
apply mapsto_memory_block.memory_block_conflict; auto.
Qed.

(* TODO: merge size_compatible and align_compatible *)
Definition align_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => align_compatible_rec cenv_cs t (Ptrofs.unsigned i_ofs)
  | _ => True
  end.

Definition size_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => Ptrofs.unsigned i_ofs + sizeof t < Ptrofs.modulus
  | _ => True
  end.

Lemma mapsto_valid_pointer: forall {cs: compspecs} sh t p v i,
  size_compatible t p ->
  0 <= i < sizeof t ->
  sepalg.nonidentity sh ->
  mapsto sh t p v |-- valid_pointer (offset_val i p).
Proof. exact @mapsto_valid_pointer. Qed.

Lemma memory_block_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i < n ->
  sepalg.nonidentity sh ->
  memory_block sh n p |-- valid_pointer (offset_val i p).
Proof. exact @memory_block_valid_pointer. Qed.

Lemma memory_block_weak_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i <= n -> 0 < n -> sepalg.nonidentity sh ->
  memory_block sh n p |-- weak_valid_pointer (offset_val i p).
Proof. exact @memory_block_weak_valid_pointer. Qed.

Lemma mapsto_zeros_memory_block: forall sh n p,
  readable_share sh ->
  mapsto_zeros n sh p |--
  memory_block sh n p.
Proof. exact mapsto_memory_block.mapsto_zeros_memory_block. Qed.

Lemma mapsto_pointer_void:
  forall sh t a, 
    eqb_type (Tpointer t a) int_or_ptr_type = false ->
    eqb_type (Tpointer Tvoid a) int_or_ptr_type = false ->
    mapsto sh (Tpointer t a) = mapsto sh (Tpointer Tvoid a).
Proof. exact mapsto_memory_block.mapsto_pointer_void. Qed.

Lemma mapsto_unsigned_signed:
 forall sign1 sign2 sh sz v i,
  mapsto sh (Tint sz sign1 noattr) v (Vint (Cop.cast_int_int sz sign1 i)) =
  mapsto sh (Tint sz sign2 noattr) v (Vint (Cop.cast_int_int sz sign2 i)).
Proof. exact Clight_mapsto_memory_block.mapsto_unsigned_signed. Qed.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof. exact Clight_mapsto_memory_block.mapsto_tuint_tint. Qed.

Lemma mapsto_tuint_tptr_nullval:
  forall sh p t, 
  mapsto sh (Tpointer t noattr) p nullval = mapsto sh size_t p nullval.
Proof.  exact mapsto_memory_block.mapsto_tuint_tptr_nullval. Qed.

Lemma mapsto_size_t_tptr_nullval:
  forall sh p t, mapsto sh (Tpointer t noattr) p nullval = mapsto sh size_t p nullval.
Proof. exact mapsto_memory_block.mapsto_tuint_tptr_nullval. Qed.

Definition is_int32_noattr_type t :=
 match t with
 | Tint I32 _ {| attr_volatile := false; attr_alignas := None |} => True
 | _ => False
 end.

Lemma mapsto_mapsto_int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v |-- mapsto sh t2 p v.
Proof. exact mapsto_memory_block.mapsto_mapsto_int32. Qed.

Lemma mapsto_mapsto__int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v |-- mapsto_ sh t2 p.
Proof. exact mapsto_memory_block.mapsto_mapsto__int32. Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v,
       Archi.ptr64 = false ->
             mapsto sh tint v nullval =
             mapsto sh (tptr t) v nullval.
Proof. exact Clight_mapsto_memory_block.mapsto_null_mapsto_pointer. Qed.

Definition eval_lvar (id: ident) (ty: type) (rho: environ) :=
 match Map.get (ve_of rho) id with
| Some (b, ty') => if eqb_type ty ty' then Vptr b Ptrofs.zero else Vundef
| None => Vundef
end.

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type) : environ -> mpred :=
  !! (sizeof (snd idt) <= Ptrofs.max_unsigned) &&
  `(memory_block sh (sizeof (snd idt)))
             (eval_lvar (fst idt) (snd idt)).

Definition stackframe_of {cs: compspecs} (f: Clight.function) : environ->mpred :=
  fold_right sepcon emp (map (var_block Tsh) (fn_vars f)).

Lemma  subst_derives {A}{NA: NatDed A}:
 forall a v (P Q: environ -> A), P |-- Q -> subst a v P |-- subst a v Q.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && seplog.func_at f (b, 0).

Lemma corable_func_ptr: forall f v, corable (func_ptr f v).
Proof.
  intros.
  unfold func_ptr.
  apply corable_exp; intro.
  apply corable_andp; auto.
  apply assert_lemmas.corable_func_at.
Qed.

Lemma func_ptr_isptr: forall spec f, func_ptr spec f |-- !! isptr f.
Proof.
  intros.
  unfold func_ptr.
  destruct spec.
  normalize.
Qed.

Definition NDmk_funspec (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> environ -> mpred): funspec :=
  mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
    (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Lemma approx_func_ptr: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  compcert_rmaps.RML.R.approx n (func_ptr (NDmk_funspec fsig0 cc A P Q) v) = compcert_rmaps.RML.R.approx n (func_ptr (NDmk_funspec fsig0 cc A (fun a rho => compcert_rmaps.RML.R.approx n (P a rho)) (fun a rho => compcert_rmaps.RML.R.approx n (Q a rho))) v).
Proof.
  exact seplog.approx_func_ptr.
Qed.

Definition allp_fun_id (Delta : tycontext): environ -> mpred :=
(ALL id : ident ,
 (ALL fs : funspec ,
  !! ((glob_specs Delta) ! id = Some fs) -->
  (EX b : block, local (`eq (fun rho => Map.get (ge_of rho) id) `(Some b)) && `(seplog.func_at fs (b, 0))))).

Lemma corable_allp_fun_id: forall Delta rho,
  corable (allp_fun_id Delta rho).
Proof.
  intros.
  unfold allp_fun_id; simpl.
  apply corable_allp; intros id.
  apply corable_allp; intros fs.
  apply corable_imp; [apply corable_prop |].
  apply corable_exp; intros b.
  apply corable_andp; [apply corable_prop |].
  apply assert_lemmas.corable_func_at.
Qed.

Definition type_of_funsig (fsig: funsig) :=
   Tfunction (type_of_params (fst fsig)) (snd fsig) cc_default.
Definition fn_funsig (f: function) : funsig := (fn_params f, fn_return f).

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with
 | None => True
 | Some i => match (temp_types Delta) ! i with Some t' => t=t' | _ => False end
 end.

Definition globals_only (rho: environ) : environ :=
    mkEnviron (ge_of rho) (Map.empty _) (Map.empty _).

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho
 end.
Definition make_args' (fsig: funsig) args rho :=
   make_args (map (@fst _ _) (fst fsig)) (args rho) rho.

Definition ret_temp : ident := 1%positive.

Definition get_result1 (ret: ident) (rho: environ) : environ :=
   make_args (ret_temp::nil) (eval_id ret rho :: nil) rho.

Definition get_result (ret: option ident) : environ -> environ :=
 match ret with
 | None => make_args nil nil
 | Some x => get_result1 x
 end.

Definition maybe_retval (Q: environ -> mpred) retty ret :=
 match ret with
 | Some id => fun rho => Q (get_result1 id rho)
 | None =>
    match retty with
    | Tvoid => (fun rho => Q (globals_only rho))
    | _ => fun rho => EX v: val, Q (make_args (ret_temp::nil) (v::nil) rho)
    end
 end.

Definition bind_ret (vl: option val) (t: type) (Q: environ -> mpred) : environ -> mpred :=
     match vl, t with
     | None, Tvoid =>`Q (make_args nil nil)
     | Some v, _ => @andp (environ->mpred) _ (!! tc_val t v)
                             (`Q (make_args (ret_temp::nil) (v::nil)))
     | _, _ => FF
     end.

Definition overridePost  (Q: environ->mpred)  (R: ret_assert) :=
 match R with 
  {| RA_normal := _; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Q; RA_break := b; RA_continue := c; RA_return := r |}
 end.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) :=
  {| RA_normal := fun rho => EX x:A, (R x).(RA_normal) rho;
     RA_break := fun rho => EX x:A, (R x).(RA_break) rho;
     RA_continue := fun rho => EX x:A, (R x).(RA_continue) rho;
     RA_return := fun vl rho => EX x:A, (R x).(RA_return) vl rho
   |}.

Definition normal_ret_assert (Q: environ->mpred) : ret_assert :=
  {| RA_normal := Q; RA_break := seplog.FF; RA_continue := seplog.FF; RA_return := fun _ => seplog.FF |}.

Definition frame_ret_assert (R: ret_assert) (F: environ->mpred) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := n * F; 
     RA_break := b * F; 
     RA_continue := c * F;
     RA_return := fun vl => r vl * F |}
 end.

Definition switch_ret_assert (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := FF; 
     RA_break := n; 
     RA_continue := c;
     RA_return := r |}
 end.

Definition with_ge (ge: genviron) (G: environ->mpred) : mpred :=
     G (mkEnviron ge (Map.empty _) (Map.empty _)).


Fixpoint prog_funct' {F V} (l: list (ident * globdef F V)) : list (ident * F) :=
 match l with nil => nil | (i,Gfun f)::r => (i,f):: prog_funct' r | _::r => prog_funct' r
 end.

Definition prog_funct (p: program) := prog_funct' (prog_defs p).

Fixpoint prog_vars' {F V} (l: list (ident * globdef F V)) : list (ident * globvar V) :=
 match l with nil => nil | (i,Gvar v)::r => (i,v):: prog_vars' r | _::r => prog_vars' r
 end.

Definition prog_vars (p: program) := prog_vars' (prog_defs p).

Definition all_initializers_aligned (prog: program) :=
  forallb (fun idv => andb (initializers_aligned 0 (gvar_init (snd idv)))
                                 (Zlt_bool (init_data_list_size (gvar_init (snd idv))) Ptrofs.modulus))
                      (prog_vars prog) = true.

Definition loop1_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := Inv;
     RA_return := r |}
 end.

Definition loop2_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n;
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Definition function_body_ret_assert (ret: type) (Q: environ->mpred) : ret_assert :=
 {| RA_normal := seplog.FF;
    RA_break := seplog.FF; 
    RA_continue := seplog.FF;
    RA_return := fun vl => bind_ret vl ret Q |}.

Definition loop_nocontinue_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Definition tc_environ (Delta: tycontext) : environ -> Prop :=
   fun rho => typecheck_environ Delta rho.

Definition tc_temp_id  (id: ident)  (ty: type) {CS: compspecs} (Delta: tycontext)
                       (e:expr): environ -> mpred :=
      denote_tc_assert (typecheck_temp_id id ty Delta e).

(* TODO: remove this kind of definitions. *)
Definition typeof_temp (Delta: tycontext) (id: ident) : option type :=
 match (temp_types Delta) ! id with
 | Some t => Some t
 | None => None
 end.

Definition tc_expr {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred :=
    denote_tc_assert (typecheck_expr Delta e).

Definition tc_exprlist {CS: compspecs} (Delta: tycontext) (t: list type) (e: list expr)  : environ -> mpred :=
      denote_tc_assert (typecheck_exprlist Delta t e).

Definition tc_lvalue {CS: compspecs} (Delta: tycontext) (e: expr) : environ -> mpred :=
     denote_tc_assert (typecheck_lvalue Delta e).

Definition tc_expropt {CS: compspecs} Delta (e: option expr) (t: type) : environ -> mpred :=
   match e with None => `!!(t=Tvoid)
                     | Some e' => tc_expr Delta (Ecast e' t)
   end.

Definition is_comparison op :=
match op with
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => true
  | _ => false
end.

Definition blocks_match op v1 v2  :=
match op with Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge =>
  match v1, v2 with
    Vptr b _, Vptr b2 _ => b=b2
    | _, _ => False
  end
| _ => True
end.

Definition cmp_ptr_no_mem c v1 v2  :=
match v1, v2 with
Vptr b o, Vptr b1 o1 =>
  if peq b b1 then
    Val.of_bool (Ptrofs.cmpu c o o1)
  else
    match Val.cmp_different_blocks c with
    | Some b => Val.of_bool b
    | None => Vundef
    end
| _, _ => Vundef
end.

Definition op_to_cmp cop :=
match cop with
| Cop.Oeq => Ceq | Cop.One =>  Cne
| Cop.Olt => Clt | Cop.Ogt =>  Cgt
| Cop.Ole => Cle | Cop.Oge =>  Cge
| _ => Ceq (*doesn't matter*)
end.

Fixpoint arglist (n: positive) (tl: typelist) : list (ident*type) :=
 match tl with
  | Tnil => nil
  | Tcons t tl' => (n,t):: arglist (n+1)%positive tl'
 end.

Definition closed_wrt_modvars c (F: environ->mpred) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , init_data_list_size (gvar_init l)) end.

Definition main_pre (prog: program) : list Type -> globals -> environ -> mpred :=
(fun nil gv => globvars2pred gv (prog_vars prog)).

Definition main_pre_ext {Espec: OracleKind} (prog: program) (ora: OK_ty) : list Type -> globals -> environ -> mpred :=
(fun nil gv rho => globvars2pred gv (prog_vars prog) rho * has_ext ora).

Definition main_post (prog: program) : list Type -> (ident->val) -> environ->mpred :=
  (fun nil _ _ => TT).


Definition main_spec' (prog: program) 
    (post: list Type -> globals -> environ -> mpred): funspec :=
  mk_funspec (nil, tint) cc_default
     (rmaps.ConstType globals) (main_pre prog) post
       (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition main_spec (prog: program): funspec :=
  mk_funspec (nil, tint) cc_default
     (rmaps.ConstType globals) (main_pre prog) (main_post prog)
       (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition main_spec_ext' {Espec: OracleKind} (prog: program) (ora: OK_ty)
    (post: list Type -> globals -> environ -> mpred): funspec :=
  mk_funspec (nil, tint) cc_default
     (rmaps.ConstType globals) (main_pre_ext prog ora) post
       (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Definition main_spec_ext {Espec: OracleKind} (prog: program) (ora: OK_ty) : funspec :=
  mk_funspec (nil, tint) cc_default
     (rmaps.ConstType globals) (main_pre_ext prog ora) (main_post prog)
       (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Fixpoint match_globvars (gvs: list (ident * globvar type)) (V: varspecs) : bool :=
 match V with
 | nil => true
 | (id,t)::V' => match gvs with
                       | nil => false
                       | (j,g)::gvs' => if eqb_ident id j
                                              then andb (eqb_type t (gvar_info g)) (match_globvars gvs' V')
                                              else match_globvars gvs' V
                      end
  end.

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

Lemma mapsto_value_range:
 forall sh v sz sgn i,
   readable_share sh ->
   mapsto sh (Tint sz sgn noattr) v (Vint i) =
    !! int_range sz sgn i && mapsto sh (Tint sz sgn noattr) v (Vint i).
Proof. exact mapsto_memory_block.mapsto_value_range. Qed.

Definition semax_body_params_ok f : bool :=
   andb
        (compute_list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)))
        (compute_list_norepet (map (@fst _ _) (fn_vars f))).

Definition var_sizes_ok {cs: compspecs} (vars: list (ident*type)) :=
   Forall (fun var : ident * type => sizeof (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition make_ext_rval  (gx: genviron) (v: option val):=
  match v with
  | Some v' =>  mkEnviron gx (Map.empty _)
                              (Map.set 1%positive v' (Map.empty _))
  | None => mkEnviron gx (Map.empty _) (Map.empty _)
  end.

Definition tc_option_val (sig: type) (ret: option val) :=
  match sig, ret with
    | Tvoid, None => True
    | Tvoid, Some _ => False
    | ty, Some v => tc_val ty v
    | _, _ => False
  end.

Fixpoint zip_with_tl {A : Type} (l1 : list A) (l2 : typelist) : list (A*type) :=
  match l1, l2 with
    | a::l1', Tcons b l2' => (a,b)::zip_with_tl l1' l2'
    | _, _ => nil
  end.

Definition  funspecs_norepeat (fs : funspecs) := list_norepet (map fst fs).

Require VST.veric.semax_ext.

Definition add_funspecs (Espec : OracleKind)
         (ext_link: Strings.String.string -> ident)
         (fs : funspecs) : OracleKind :=
   veric.semax_ext.add_funspecs Espec ext_link fs.

Definition funsig2signature (s : funsig) cc : signature :=
  mksignature (map typ_of_type (map snd (fst s))) (opttyp_of_type (snd s)) cc.

Transparent mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric Bveric.

(* Misc lemmas *)
Lemma typecheck_lvalue_sound {CS: compspecs} :
  forall Delta rho e,
    typecheck_environ Delta rho ->
    tc_lvalue Delta e rho |-- !! is_pointer_or_null (eval_lvalue e rho).
Proof.
intros.
intros ? ?.
eapply expr_lemmas4.typecheck_lvalue_sound; eauto.
Qed.

Lemma typecheck_expr_sound {CS: compspecs} :
  forall Delta rho e,
    typecheck_environ Delta rho ->
    tc_expr Delta e rho |-- !! tc_val (typeof e) (eval_expr e rho).
Proof.
intros.
intros ? ?.
simpl.
eapply expr_lemmas4.typecheck_expr_sound; eauto.
Qed.

(* End misc lemmas *)

(* BEGIN rel_expr stuff *)
Lemma rel_expr_const_int: forall {CS: compspecs} i ty P rho,
              P |-- rel_expr (Econst_int i ty) (Vint i) rho.
Proof. intros. intros ? ?; constructor. Qed.

Lemma rel_expr_const_float: forall {CS: compspecs}  f ty P rho,
              P |-- rel_expr (Econst_float f ty) (Vfloat f) rho.
Proof. intros. intros ? ?; constructor. Qed.

Lemma rel_expr_const_single: forall {CS: compspecs}   f ty P rho,
              P |-- rel_expr (Econst_single f ty) (Vsingle f) rho.
Proof. intros. intros ? ?; constructor. Qed.

Lemma rel_expr_const_long: forall {CS: compspecs}  i ty P rho,
             P |--  rel_expr (Econst_long i ty) (Vlong i) rho.
Proof. intros. intros ? ?; constructor. Qed.

Lemma rel_expr_tempvar: forall {CS: compspecs}  id ty v P rho,
          Map.get (te_of rho) id = Some v ->
          P |-- rel_expr (Etempvar id ty) v rho.
Proof. intros. intros ? ?. constructor; auto. Qed.

Lemma rel_expr_addrof: forall {CS: compspecs} a ty v P rho,
               P |-- rel_lvalue a v rho ->
               P |-- rel_expr (Eaddrof a ty) v rho.
Proof. intros. intros ? ?. constructor; auto. apply H; auto. Qed.

Lemma rel_expr_unop: forall {CS: compspecs}  P a1 v1 v ty op rho,
                 P |-- rel_expr a1 v1 rho ->
                 (forall m, Cop.sem_unary_operation op v1 (typeof a1) m = Some v) ->
                 P |-- rel_expr (Eunop op a1 ty) v rho.
Proof.
intros. intros ? ?. econstructor; eauto. apply H; auto. Qed.

Lemma rel_expr_binop: forall {CS: compspecs}  a1 a2 v1 v2 v ty op P rho,
                 P |-- rel_expr a1 v1 rho ->
                 P |-- rel_expr  a2 v2 rho ->
                 binop_stable cenv_cs op a1 a2 = true ->
                 (forall m, Cop.sem_binary_operation cenv_cs op v1 (typeof a1) v2 (typeof a2) m = Some v) ->
                 P |-- rel_expr (Ebinop op a1 a2 ty) v rho.
Proof.
intros. intros ? ?. econstructor; eauto. apply H; auto. apply H0; auto. Qed.

Lemma rel_expr_cast: forall {CS: compspecs}  a1 v1 v ty P rho,
                 P |-- rel_expr a1 v1 rho ->
                 (forall m, Cop.sem_cast v1 (typeof a1) ty m = Some v) ->
                 P |-- rel_expr (Ecast a1 ty) v rho.
Proof.
intros. intros ? ?. econstructor; eauto. apply H; auto. Qed.

Lemma rel_expr_lvalue_By_value: forall {CS: compspecs} ch a sh v1 v2 P rho,
           access_mode (typeof a) = By_value ch ->
           P |-- rel_lvalue a v1 rho ->
           P |-- mapsto sh (typeof a) v1 v2 * TT  ->
           v2 <> Vundef ->
           readable_share sh ->
           P |-- rel_expr a v2 rho.
Proof.
intros. intros ? ?.
econstructor; eauto.
+ apply H0; auto.
+ apply H1; auto.
Qed.

Lemma rel_expr_lvalue_By_reference: forall {CS: compspecs} a v1 P rho,
           access_mode (typeof a) = By_reference ->
           P |-- rel_lvalue a v1 rho ->
           P |-- rel_expr a v1 rho.
Proof.
intros. intros ? ?.
hnf.
eapply rel_expr'_lvalue_By_reference; eauto.
apply H0; auto.
 Qed.

Lemma rel_lvalue_local: forall {CS: compspecs} id ty b P rho,
                 P |-- !! (Map.get (ve_of rho) id = Some (b,ty)) ->
                 P |-- rel_lvalue (Evar id ty) (Vptr  b Ptrofs.zero) rho.
Proof.
intros. intros ? ?. constructor.  specialize (H _ H0). apply H.
Qed.

Lemma rel_lvalue_global: forall {CS: compspecs} id ty b P rho,
              P |-- !! (Map.get (ve_of rho) id = None /\ Map.get (ge_of rho) id = Some b) ->
              P |-- rel_lvalue (Evar id ty) (Vptr b Ptrofs.zero) rho.
Proof.
intros. intros ? ?. specialize (H _ H0). destruct H. constructor 2; auto.
Qed.

Lemma rel_lvalue_deref: forall {CS: compspecs} a b z ty P rho,
              P |-- rel_expr a (Vptr b z) rho->
              P |-- rel_lvalue (Ederef a ty) (Vptr b z) rho.
Proof. intros. intros ? ?. constructor. apply H. auto. Qed.

Lemma rel_lvalue_field_struct: forall {CS: compspecs}  i ty a b z id att delta co P rho,
               typeof a = Tstruct id att ->
               cenv_cs ! id = Some co ->
               field_offset cenv_cs i (co_members co) = Errors.OK delta ->
               P |-- rel_lvalue a (Vptr b z) rho ->
               P |-- rel_lvalue (Efield a i ty) (Vptr b (Ptrofs.add z (Ptrofs.repr delta))) rho.
Proof.
intros. intros ? ?. econstructor; eauto. apply H2; auto. Qed.

Global Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric Bveric.
Global Opaque rel_expr.
Global Opaque rel_lvalue.

(* END rel_expr stuff *)

(* Don't know why this next Hint doesn't work unless fully instantiated;
   perhaps because one needs both "contractive" and "typeclass_instances"
   Hint databases if this next line is not added. *)
Hint Resolve (@subp_sepcon mpred Nveric Iveric Sveric SIveric Rveric SRveric): contractive.

Fixpoint unfold_Ssequence c :=
  match c with
  | Ssequence c1 c2 => unfold_Ssequence c1 ++ unfold_Ssequence c2
  | _ => c :: nil
  end.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Parameter semax: forall {CS: compspecs} {Espec: OracleKind},
    tycontext -> (environ->mpred) -> statement -> ret_assert -> Prop.

Parameter semax_func:
    forall {Espec: OracleKind},
    forall (V: varspecs) (G: funspecs) {C: compspecs} (fdecs: list (ident * fundef)) (G1: funspecs), Prop.

Parameter semax_external:
  forall {Hspec: OracleKind} (ids: list ident) (ef: external_function)
  (A: rmaps.TypeTree)
  (P Q: forall ts, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred),
     Prop.

End CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module DerivedDefs (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF).

Local Open Scope pred.

Definition semax_body
       (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=
  match spec with (_, mk_funspec _ cc A P Q NEP NEQ) =>
    forall Espec ts x, (*exists Ann,*)
      @Def.semax C Espec (func_tycontext f V G nil (*Ann*))
          (P ts x *  stackframe_of f)
          (Ssequence f.(fn_body) (Sreturn None))
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))
 end.

Definition semax_prog
    {Espec: OracleKind} {C: compspecs}
     (prog: program)  (V: varspecs) (G: funspecs) : Prop :=
  compute_list_norepet (prog_defs_names prog) = true  /\
  all_initializers_aligned prog /\
  cenv_cs = prog_comp_env prog /\
  @Def.semax_func Espec V G C (prog_funct prog) G /\
  match_globvars (prog_vars prog) V = true /\
  match initial_world.find_id prog.(prog_main) G with
  | Some s => exists post, s = main_spec' prog post
  | None => False
  end.

Definition semax_prog_ext
    {Espec: OracleKind} {C: compspecs}
     (prog: program) (z : OK_ty) (V: varspecs) (G: funspecs) : Prop :=
  compute_list_norepet (prog_defs_names prog) = true  /\
  all_initializers_aligned prog /\
  cenv_cs = prog_comp_env prog /\
  @Def.semax_func Espec V G C (prog_funct prog) G /\
  match_globvars (prog_vars prog) V = true /\
  match initial_world.find_id prog.(prog_main) G with
  | Some s => exists post, s = main_spec_ext' prog z post
  | None => False
  end.

End DerivedDefs.

Module Type MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module CSHL_Defs := DerivedDefs(CSHL_Def).

Import CSHL_Def.
Import CSHL_Defs.

(***************** SEMAX_LEMMAS ****************)

Axiom semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type) (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.

Axiom semax_func_nil:   forall {Espec: OracleKind},
        forall V G C, @semax_func Espec V G C nil nil.

Axiom semax_func_cons:
  forall {Espec: OracleKind},
     forall fs id f cc A P Q NEP NEQ (V: varspecs) (G G': funspecs) {C: compspecs},
      andb (id_in_list id (map (@fst _ _) G))
      (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
        (semax_body_params_ok f)) = true ->
      Forall
         (fun it : ident * type =>
          complete_type cenv_cs (snd it) =
          true) (fn_vars f) ->
       var_sizes_ok (f.(fn_vars)) ->
       f.(fn_callconv) = cc ->
       precondition_closed f P ->
      semax_body V G f (id, mk_funspec (fn_funsig f) cc A P Q NEP NEQ)->
      semax_func V G fs G' ->
      semax_func V G ((id, Internal f)::fs)
           ((id, mk_funspec (fn_funsig f) cc A P Q NEP NEQ)  :: G').

Axiom semax_func_cons_ext:
  forall {Espec: OracleKind},
   forall (V: varspecs) (G: funspecs) {C: compspecs} fs id ef argsig retsig A P Q NEP NEQ
          argsig'
          (G': funspecs) cc (ids: list ident),
      ids = map fst argsig' -> (* redundant but useful for the client,
               to calculate ids by reflexivity *)
      argsig' = zip_with_tl ids argsig ->
      ef_sig ef =
      mksignature
        (typlist_of_typelist (type_of_params argsig'))
        (opttyp_of_type retsig) cc ->
      id_in_list id (map (@fst _ _) fs) = false ->
      length ids = length (typelist2list argsig) ->
      (forall gx ts x (ret : option val),
         (Q ts x (make_ext_rval gx ret)
            && !!step_lemmas.has_opttyp ret (opttyp_of_type retsig)
            |-- !!tc_option_val retsig ret)) ->
      @semax_external Espec ids ef A P Q ->
      semax_func V G fs G' ->
      semax_func V G ((id, External ef argsig retsig cc)::fs)
           ((id, mk_funspec (argsig', retsig) cc A P Q NEP NEQ)  :: G').

(* THESE RULES FROM semax_loop *)

Axiom semax_ifthenelse :
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P) (Sifthenelse b c d) R.

Axiom semax_seq:
  forall{CS: compspecs} {Espec: OracleKind},
forall Delta R P Q h t,
    @semax CS Espec Delta P h (overridePost Q R) ->
    @semax CS Espec Delta Q t R ->
    @semax CS Espec Delta P (Ssequence h t) R.

Axiom semax_break:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta Q,    @semax CS Espec Delta (RA_break Q) Sbreak Q.

Axiom semax_continue:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta Q,    @semax CS Espec Delta (RA_continue Q) Scontinue Q.

Axiom semax_loop :
  forall{CS: compspecs} {Espec: OracleKind},
forall Delta Q Q' incr body R,
     @semax CS Espec Delta  Q body (loop1_ret_assert Q' R) ->
     @semax CS Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax CS Espec Delta Q (Sloop body incr) R.

(* THIS RULE FROM semax_switch *)

Axiom semax_switch: 
  forall{CS: compspecs} {Espec: OracleKind},
  forall Delta (Q: environ->mpred) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta Q (Sswitch a sl) R.

(* THESE RULES FROM semax_call *)
(*
Parameter func_ptr : funspec -> val ->mpred.
Axiom corable_func_ptr: forall f v, corable (func_ptr f v).
Axiom func_ptr_isptr: forall spec f, func_ptr spec f |-- !! isptr f.

Axiom approx_func_ptr: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
    compcert_rmaps.RML.R.approx n (func_ptr (NDmk_funspec fsig0 cc A P Q) v) = compcert_rmaps.RML.R.approx n (func_ptr (NDmk_funspec fsig0 cc A (fun a rho => compcert_rmaps.RML.R.approx n (P a rho)) (fun a rho => compcert_rmaps.RML.R.approx n (Q a rho))) v).

Axiom func_ptr_def :
  func_ptr = fun f v => EX b : block, !!(v = Vptr b Ptrofs.zero) && seplog.func_at f (b, 0).*)
Axiom semax_call :
  forall {CS: compspecs} {Espec: OracleKind},
    forall Delta A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).

Axiom  semax_return :
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R.

(* THESE RULES FROM semax_straight *)

Axiom semax_set_forward :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).

Axiom semax_ptr_compare :
forall{CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                            subst id `(old) P)).

Axiom semax_load :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (`v2)) &&
                                          (subst id (`old) P))).

Axiom semax_cast_load :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (`(eval_cast (typeof e1) t1 v2))) &&
                                          (subst id (`old) P))).

Axiom semax_store:
  forall {CS: compspecs} {Espec: OracleKind},
 forall Delta e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
               (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).

(* THESE RULES FROM semax_lemmas *)

Axiom semax_skip:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P, @semax CS Espec Delta P Sskip (normal_ret_assert P).

Axiom semax_conseq:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P' (R': ret_assert) P c (R: ret_assert) ,
    local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- |==> |> FF || P' ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- |==> |> FF || RA_normal R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- |==> |> FF || RA_break R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- |==> |> FF || RA_continue R ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- |==> |> FF || RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

Axiom semax_Slabel:
   forall {cs:compspecs} {Espec: OracleKind},
     forall Delta (P:environ -> mpred) (c:statement) (Q:ret_assert) l,
   @semax cs Espec Delta P c Q -> @semax cs Espec Delta P (Slabel l c) Q.

(* THESE RULES FROM semax_ext *)

(*TODO: What's the preferred way to expose these defs in the SL interface?*)

Axiom semax_ext:
  forall  (Espec : OracleKind)
         (ext_link: Strings.String.string -> ident)
         (id : Strings.String.string) (ids : list ident) (sig : funsig) (sig' : signature)
         cc A P Q NEP NEQ (fs : funspecs),
  let f := mk_funspec sig cc A P Q NEP NEQ in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  ids = fst (split (fst sig)) ->
  sig' = funsig2signature sig cc ->
  @semax_external (add_funspecs Espec ext_link fs) ids (EF_external id sig') _ P Q.

Axiom semax_ext_void:
  forall  (Espec : OracleKind)
         (ext_link: Strings.String.string -> ident)
         (id : Strings.String.string) (ids : list ident) sig (sig' : signature)
         cc A P Q NEP NEQ (fs : funspecs),
  let f := mk_funspec (sig, tvoid) cc A P Q NEP NEQ in
  In (ext_link id,f) fs ->
  funspecs_norepeat fs ->
  ids = fst (split sig) ->
  sig' = mksignature (map typ_of_type (map snd sig)) None cc ->
  @semax_external (add_funspecs Espec ext_link fs) ids (EF_external id sig') _ P Q.

Axiom semax_external_FF:
 forall Espec ids ef A,
  @semax_external Espec ids ef A (fun _ _ => FF) (fun _ _ => FF).

End MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Module Type PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.

Declare Module CSHL_MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC.

Import CSHL_MinimumLogic.CSHL_Def.
Import CSHL_MinimumLogic.CSHL_Defs.

Axiom semax_set :
  forall {CS: compspecs} {Espec: OracleKind},
forall (Delta: tycontext) (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).

Axiom semax_fun_id:
  forall {CS: compspecs} {Espec: OracleKind},
      forall id f Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_specs Delta) ! id = Some f ->
    (glob_types Delta) ! id = Some (type_of_funspec f) ->
    @semax CS Espec Delta (P && `(func_ptr f) (eval_var id (type_of_funspec f)))
                  c Q ->
    @semax CS Espec Delta P c Q.

Axiom semax_extensionality_Delta:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     @semax CS Espec Delta P c R -> @semax CS Espec Delta' P c R.

Axiom semax_unfold_Ssequence: forall {CS: compspecs} {Espec: OracleKind} c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, @semax CS Espec Delta P c1 Q -> @semax CS Espec Delta P c2 Q).

Axiom seq_assoc:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P s1 s2 s3 R,
        @semax CS Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        @semax CS Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.

Axiom semax_seq_skip:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s Q,
    @semax CS Espec Delta P s Q <-> @semax CS Espec Delta P (Ssequence s Sskip) Q.

Axiom semax_skip_seq:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s Q,
    @semax CS Espec Delta P s Q <-> @semax CS Espec Delta P (Ssequence Sskip s) Q.

Axiom semax_loop_nocontinue:
  forall {CS: compspecs} {Espec: OracleKind},
 forall Delta P body incr R,
 @semax CS Espec Delta P (Ssequence body incr) (loop_nocontinue_ret_assert P R) ->
 @semax CS Espec Delta P (Sloop body incr) R.

Axiom semax_loop_unroll1:
  forall {CS: compspecs} {Espec: OracleKind} Delta P P' Q body incr R,
  @semax CS Espec Delta P body (loop1_ret_assert P' R) ->
  @semax CS Espec Delta P' incr (loop2_ret_assert Q R) ->
  @semax CS Espec Delta Q (Sloop body incr) R ->
  @semax CS Espec Delta P (Sloop body incr) R.

Axiom semax_if_seq:
 forall {CS: compspecs} {Espec: OracleKind} Delta P e c1 c2 c Q,
 semax Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.

Axiom semax_seq_Slabel:
   forall {cs:compspecs} {Espec: OracleKind},
     forall Delta (P:environ -> mpred) (c1 c2:statement) (Q:ret_assert) l,
   @semax cs Espec Delta P (Ssequence (Slabel l c1) c2) Q <-> 
   @semax cs Espec Delta P (Slabel l (Ssequence c1 c2)) Q.

(**************** END OF stuff from semax_rules ***********)

Axiom semax_frame:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s R F,
   closed_wrt_modvars s F ->
  @semax CS Espec Delta P s R ->
    @semax CS Espec Delta (P * F) s (frame_ret_assert R F).

Axiom semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (!!PP && P) c Q.

Axiom semax_extract_later_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta ((|> !!PP) && P) c Q.

End PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.

Require Import Coq.Classes.Morphisms.

Instance prop_Proper:
  Proper (iff ==> (@eq mpred)) (prop).
Proof.
  intros ? ? ?.
  apply ND_prop_ext.
  auto.
Defined.