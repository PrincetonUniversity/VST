Require Export compcert.lib.Axioms.
Require Import Coqlib.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export compcert.common.Values.
Require Export Maps.
Require Export Ctypes.
Require Export Clight.
Require Export sepcomp.Address.
Require Export msl.eq_dec.
Require Export msl.shares.
Require Export msl.seplog.
Require Export msl.alg_seplog.
Require Export msl.log_normalize.
Require Export veric.expr.
Require veric.seplog.
Require veric.assert_lemmas. 
Require Import sepcomp.Coqlib2.
Require Import veric.juicy_extspec.

Instance Nveric: NatDed mpred := algNatDed compcert_rmaps.RML.R.rmap.
Instance Sveric: SepLog mpred := algSepLog compcert_rmaps.RML.R.rmap.
Instance Cveric: ClassicalSep mpred := algClassicalSep compcert_rmaps.RML.R.rmap.
Instance Iveric: Indir mpred := algIndir compcert_rmaps.RML.R.rmap.
Instance Rveric: RecIndir mpred := algRecIndir compcert_rmaps.RML.R.rmap.
Instance SIveric: SepIndir mpred := algSepIndir compcert_rmaps.RML.R.rmap.
Instance SRveric: SepRec mpred := algSepRec compcert_rmaps.RML.R.rmap.

Instance LiftNatDed' T {ND: NatDed T}: NatDed (LiftEnviron T) := LiftNatDed _ _.
Instance LiftSepLog' T {ND: NatDed T}{SL: SepLog T}: SepLog (LiftEnviron T) := LiftSepLog _ _.
Instance LiftClassicalSep' T {ND: NatDed T}{SL: SepLog T}{CS: ClassicalSep T} :
           ClassicalSep (LiftEnviron T) := LiftClassicalSep _ _.
Instance LiftIndir' T {ND: NatDed T}{SL: SepLog T}{IT: Indir T} :
           Indir (LiftEnviron T) := LiftIndir _ _.
Instance LiftSepIndir' T {ND: NatDed T}{SL: SepLog T}{IT: Indir T}{SI: SepIndir T} :
           SepIndir (LiftEnviron T) := LiftSepIndir _ _.

Definition local:  (environ -> Prop) -> environ->mpred :=  lift1 prop.

Global Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.

Hint Resolve any_environ : typeclass_instances.

Definition ret_assert := exitkind -> option val -> environ -> mpred.

Definition address_mapsto: memory_chunk -> val -> Share.t -> Share.t -> address -> mpred := 
       res_predicates.address_mapsto.

Local Open Scope logic.

Bind Scope pred with mpred.
Local Open Scope pred.

Definition closed_wrt_vars {B} (S: ident -> Prop) (F: environ -> B) : Prop := 
  forall rho te',  
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
Some false.

Definition subst {A} (x: ident) (v: environ -> val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x (v s)).

Definition substopt {A} (ret: option ident) (v: environ -> val) (P: environ -> A)  : environ -> A :=
   match ret with
   | Some id => subst id v P
   | None => P
   end.

Definition cast_expropt (e: option expr) t : environ -> option val :=
 match e with Some e' => `Some (eval_expr (Ecast e' t))  | None => `None end.

Definition typecheck_tid_ptr_compare
Delta id := 
match (temp_types Delta) ! id with
| Some (t, _) =>
   is_int_type t 
| None => false
end. 

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch => 
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs => 
          (!!tc_val t v2 && address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs))
        || !! (v2 = Vundef) && EX v2':val, address_mapsto ch v2' (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)
     | _ => FF
    end
    | _ => FF
    end
  | _ => FF
  end. 

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Definition Tsh : share := Share.top.

Definition writable_share: share -> Prop := fun sh => Share.unrel Share.Rsh sh = Tsh.

Fixpoint address_mapsto_zeros (sh: share) (n: nat) (adr: address) : mpred :=
 match n with
 | O => emp
 | S n' => address_mapsto Mint8unsigned (Vint Int.zero)
                (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) adr 
               * address_mapsto_zeros sh n' (fst adr, Zsucc (snd adr))
end.

Definition mapsto_zeros (n: Z) (sh: share) (a: val) : mpred :=
 match a with
  | Vptr b z => address_mapsto_zeros sh (nat_of_Z n)
                          (b, Int.unsigned z)
  | _ => TT
  end.

Definition init_data2pred (d: init_data)  (sh: share) (a: val) (rho: environ) : mpred :=
 match d with
  | Init_int8 i => mapsto sh (Tint I8 Unsigned noattr) a (Vint (Int.zero_ext 8 i))
  | Init_int16 i => mapsto sh (Tint I16 Unsigned noattr) a (Vint (Int.zero_ext 16 i))
  | Init_int32 i => mapsto sh (Tint I32 Unsigned noattr) a (Vint i)
  | Init_int64 i => mapsto sh (Tlong Unsigned noattr) a (Vlong i)
  | Init_float32 r =>  mapsto sh (Tfloat F32 noattr) a (Vfloat ((Float.singleoffloat r)))
  | Init_float64 r =>  mapsto sh (Tfloat F64 noattr) a (Vfloat r)
  | Init_space n => mapsto_zeros n sh a
  | Init_addrof symb ofs =>
       match ge_of rho symb with
       | Some (v, Tarray t _ _) => mapsto sh (Tpointer t noattr) a (offset_val ofs v)
       | Some (v, Tvoid) => TT
       | Some (v, t) => mapsto sh (Tpointer t noattr) a (offset_val ofs v)
       | _ => TT
       end
 end.

Definition extern_retainer : share := Share.Lsh.

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => 4
  | Init_space n => Zmax n 0
  end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Fixpoint init_data_list2pred (dl: list init_data) 
                           (sh: share) (v: val)  (rho: environ) : mpred :=
  match dl with
  | d::dl' => 
      sepcon (init_data2pred d (Share.splice extern_retainer sh) v rho) 
                  (init_data_list2pred dl' sh (offset_val (Int.repr (init_data_size d)) v) rho)
  | nil => emp
 end.

Definition readonly2share (rdonly: bool) : share :=
  if rdonly then Share.Lsh else Tsh.

Definition globvar2pred (idv: ident * globvar type) : environ->mpred :=
 fun rho =>
  match ge_of rho (fst idv) with
  | None => emp
  | Some (v, t) => if (gvar_volatile (snd idv))
                       then  TT
                       else    init_data_list2pred (gvar_init (snd idv))
                                   (readonly2share (gvar_readonly (snd idv))) v rho
 end.

Definition globvars2pred (vl: list (ident * globvar type)) : environ->mpred :=
  fold_right sepcon emp (map globvar2pred vl).

Definition initializer_aligned (z: Z) (d: init_data) : bool :=
  match d with
  | Init_int16 n => Zeq_bool (z mod 2) 0
  | Init_int32 n => Zeq_bool (z mod 4) 0
  | Init_int64 n => Zeq_bool (z mod 8) 0
  | Init_float32 n =>  Zeq_bool (z mod 4) 0
  | Init_float64 n =>  Zeq_bool (z mod 8) 0
  | Init_addrof symb ofs =>  Zeq_bool (z mod 4) 0
  | _ => true
  end.
  
Fixpoint initializers_aligned (z: Z) (dl: list init_data) : bool :=
  match dl with 
  | nil => true 
  | d::dl' => andb (initializer_aligned z d) (initializers_aligned (z + init_data_size d) dl')
  end.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => mapsto_ sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr i))
         * memory_block' sh n' b (i+1)
 end.

Definition memory_block (sh: share) (n: int) (v: val) : mpred :=
 match v with 
 | Vptr b ofs => memory_block' sh (nat_of_Z (Int.unsigned n)) b (Int.unsigned ofs)
 | _ => FF
 end.

Lemma memory_block'_split:
  forall sh b ofs i j,
   0 <= i <= j ->
    j <= j+ofs <= Int.max_unsigned ->
   memory_block' sh (nat_of_Z j) b ofs = 
      memory_block' sh (nat_of_Z i) b ofs * memory_block' sh (nat_of_Z (j-i)) b (ofs+i).
Proof.
intros.
rewrite seplog.memory_block'_eq; try rewrite nat_of_Z_eq; try omega.
rewrite seplog.memory_block'_eq; try rewrite nat_of_Z_eq; try omega.
rewrite seplog.memory_block'_eq; try rewrite nat_of_Z_eq; try omega.
unfold seplog.memory_block'_alt.
repeat (rewrite nat_of_Z_eq; try omega).
etransitivity ; [ | eapply res_predicates.VALspec_range_split2].
reflexivity.
omega. omega. omega.
Qed.

Definition var_block (sh: Share.t) (idt: ident * type) : environ->mpred :=
      !! (sizeof  (snd idt) <= Int.max_unsigned) &&
 `(memory_block sh (Int.repr (sizeof (snd idt))))
             (eval_var (fst idt) (snd idt)).

Definition stackframe_of (f: Clight.function) : environ->mpred :=
  fold_right sepcon emp (map (var_block Tsh) (fn_vars f)).

Lemma  subst_extens {A}{NA: NatDed A}: 
 forall a v (P Q: environ -> A), P |-- Q -> subst a v P |-- subst a v Q.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition type_of_funsig (fsig: funsig) := Tfunction (type_of_params (fst fsig)) (snd fsig).
Definition fn_funsig (f: function) : funsig := (fn_params f, fn_return f).

Definition tc_fn_return (Delta: tycontext) (ret: option ident) (t: type) :=
 match ret with 
 | None => True
 | Some i => match (temp_types Delta) ! i with Some (t',_) => t=t' | _ => False end
 end.

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tlong _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ | Tfloat _ _ => true
  | _ => false
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
     fun ek vl => if eq_dec ek EK_normal then (!! (vl=None) && Q) else R ek vl.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) := 
  fun ek vl  => EX x:A, R x ek vl .

Definition normal_ret_assert (Q: environ->mpred) : ret_assert := 
   fun ek vl => !!(ek = EK_normal) && (!! (vl = None) && Q).

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

Definition all_initializers_aligned (prog: AST.program fundef type) := 
  forallb (fun idv => andb (initializers_aligned 0 (gvar_init (snd idv)))
                                 (Zlt_bool (init_data_list_size (gvar_init (snd idv))) Int.modulus))
                      (prog_vars prog) = true.

Definition frame_ret_assert (R: ret_assert) (F: environ->mpred) : ret_assert := 
      fun ek vl => R ek vl * F.

Definition loop1_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => Inv
 | EK_break => R EK_normal None
 | EK_continue => Inv
 | EK_return => R EK_return vl
 end.

Definition loop2_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => Inv
 | EK_break => fun _ => FF
 | EK_continue => fun _ => FF 
 | EK_return => R EK_return vl
 end.

Definition function_body_ret_assert (ret: type) (Q: environ->mpred) : ret_assert := 
   fun (ek : exitkind) (vl : option val) =>
     match ek with
     | EK_return => bind_ret vl ret Q
     | _ => FF
     end.

Definition tc_environ (Delta: tycontext) : environ -> Prop :=
   fun rho => typecheck_environ Delta rho.

Definition tc_temp_id  (id: ident)  (ty: type) (Delta: tycontext) 
                       (e:expr): environ -> Prop := 
      denote_tc_assert (typecheck_temp_id id ty Delta e).

Definition typeof_temp (Delta: tycontext) (id: ident) : option type :=
 match (temp_types Delta) ! id with
 | Some (t, _) => Some t
 | None => None
 end.

Definition tc_expr (Delta: tycontext) (e: expr) : environ -> Prop := 
    denote_tc_assert (typecheck_expr Delta e).

Definition tc_exprlist (Delta: tycontext) (t: list type) (e: list expr)  : environ -> Prop := 
      denote_tc_assert (typecheck_exprlist Delta t e).

Definition tc_lvalue (Delta: tycontext) (e: expr) : environ -> Prop := 
     denote_tc_assert (typecheck_lvalue Delta e).

Definition tc_expropt Delta (e: option expr) (t: type) : environ -> Prop :=
   match e with None => `(t=Tvoid)
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
    Val.of_bool (Int.cmpu c o o1)
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

Definition exit_tycon (c: statement) (Delta: tycontext) (ek: exitkind) : tycontext :=
  match ek with 
  | EK_normal => update_tycon Delta c 
  | _ => Delta 
  end.

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , init_data_list_size (gvar_init l)) end.

Definition main_pre (prog: program) : unit -> environ->mpred := 
  (fun tt => globvars2pred (prog_vars prog)).

Definition main_post (prog: program) : unit -> environ->mpred := 
  (fun tt => TT).

Fixpoint match_globvars (gvs: list (ident * globvar type)) (V: varspecs) : bool :=
 match V with
 | nil => true 
 | (id,t)::V' => match gvs with 
                       | nil => false
                       | (j,g)::gvs' => if eqb_ident id j 
                                              then andb (is_pointer_type t) 
                                                       (andb (eqb_type t (gvar_info g)) (match_globvars gvs' V'))
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
 forall sh v sz sgn i, mapsto sh (Tint sz sgn noattr) v (Vint i) =
    !! int_range sz sgn i && mapsto sh (Tint sz sgn noattr) v (Vint i).
Proof. exact seplog.mapsto_value_range. Qed.


(* Don't know why this next Hint doesn't work unless fully instantiated;
   perhaps because one needs both "contractive" and "typeclass_instances"
   Hint databases if this next line is not added. *)
Hint Resolve (@subp_sepcon mpred Nveric Iveric Sveric SIveric Rveric SRveric): contractive.

Module Type  CLIGHT_SEPARATION_LOGIC.

Local Open Scope pred.

Parameter semax: forall {Espec: OracleKind}, 
    tycontext -> (environ->mpred) -> statement -> ret_assert -> Prop.

(***************** SEMAX_LEMMAS ****************)


Axiom extract_exists:
  forall  {Espec: OracleKind},
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: A -> ret_assert),
  (forall x, @semax Espec Delta (P x) c (R x)) ->
   @semax Espec Delta (EX x:A, P x) c (existential_ret_assert R).

Axiom semax_extensionality_Delta:
  forall {Espec: OracleKind},
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     @semax Espec Delta P c R -> @semax Espec Delta' P c R.

(** THESE RULES FROM semax_prog **)

Definition semax_body
       (V: varspecs) (G: funspecs) (f: function) (spec: ident * funspec) : Prop :=
  match spec with (_, mk_funspec _ A P Q) =>
    forall Espec x,
      @semax Espec (func_tycontext f V G)
          (P x *  stackframe_of f)
          f.(fn_body)
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f))
 end.

Parameter semax_func: 
    forall {Espec: OracleKind},
    forall (V: varspecs) (G: funspecs) (fdecs: list (ident * fundef)) (G1: funspecs), Prop.

Definition semax_prog 
    {Espec: OracleKind}
     (prog: program) (V: varspecs) (G: funspecs) : Prop :=
  compute_list_norepet (prog_defs_names prog) = true /\
  all_initializers_aligned prog /\ 
  @semax_func Espec V G (prog_funct prog) G /\
   match_globvars (prog_vars prog) V = true /\
    In (prog.(prog_main), mk_funspec (nil,Tvoid) unit (main_pre prog ) (main_post prog)) G.

Axiom semax_func_nil:   forall {Espec: OracleKind}, 
        forall V G, @semax_func Espec V G nil nil.

Definition semax_body_params_ok f : bool :=
   andb 
        (compute_list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)))
        (compute_list_norepet (map (@fst _ _) (fn_vars f))).

Axiom semax_func_cons: 
  forall {Espec: OracleKind},
     forall fs id f A P Q (V: varspecs)  (G G': funspecs),
      andb (id_in_list id (map (@fst _ _) G)) 
      (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
        (semax_body_params_ok f)) = true ->
      semax_body V G f (id, mk_funspec (fn_funsig f) A P Q ) ->
      @semax_func Espec V G fs G' ->
      @semax_func Espec V G ((id, Internal f)::fs) 
           ((id, mk_funspec (fn_funsig f) A P Q ) :: G').

Parameter semax_external:
  forall {Espec: OracleKind},
  forall (ef: external_function) (A: Type) (P Q: A -> environ->mpred),  Prop.

Axiom semax_external_FF:
  forall {Espec: OracleKind},
  forall ef A Q, @semax_external Espec ef A FF Q.

Axiom semax_func_cons_ext: 
  forall {Espec: OracleKind},
   forall (V: varspecs) (G: funspecs) fs id ef argsig retsig A P Q (G': funspecs),
      andb (id_in_list id (map (@fst _ _) G))
              (negb (id_in_list id (map (@fst _ _) fs))) = true ->
      @semax_external Espec ef A P Q ->
      @semax_func Espec V G fs G' ->
      @semax_func Espec V G ((id, External ef argsig retsig)::fs) 
           ((id, mk_funspec (arglist 1%positive argsig, retsig) A P Q)  :: G').

(* THESE RULES FROM semax_loop *)

Axiom semax_ifthenelse : 
  forall {Espec: OracleKind},
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     @semax Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R -> 
     @semax Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R -> 
     @semax Espec Delta (local (tc_expr Delta b) && P) (Sifthenelse b c d) R.

Axiom semax_seq:
  forall {Espec: OracleKind},
forall Delta R P Q h t, 
    @semax Espec Delta P h (overridePost Q R) -> 
    @semax Espec (update_tycon Delta h) Q t R -> 
    @semax Espec Delta P (Ssequence h t) R.

Axiom seq_assoc:  
  forall {Espec: OracleKind},
   forall Delta P s1 s2 s3 R,
        @semax Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        @semax Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.

Axiom semax_seq_skip:
  forall {Espec: OracleKind},
  forall Delta P s Q,
    @semax Espec Delta P s Q <-> @semax Espec Delta P (Ssequence s Sskip) Q.

Axiom semax_skip_seq:
  forall {Espec: OracleKind},
  forall Delta P s Q,
    @semax Espec Delta P s Q <-> @semax Espec Delta P (Ssequence Sskip s) Q.

Axiom semax_break:
  forall {Espec: OracleKind},
   forall Delta Q,    @semax Espec Delta (Q EK_break None) Sbreak Q.

Axiom semax_continue:
  forall {Espec: OracleKind},
   forall Delta Q,    @semax Espec Delta (Q EK_continue None) Scontinue Q.

Axiom semax_loop : 
  forall {Espec: OracleKind},
forall Delta Q Q' incr body R,
     @semax Espec Delta  Q body (loop1_ret_assert Q' R) ->
     @semax Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax Espec Delta Q (Sloop body incr) R.

(* THESE RULES FROM semax_call *)
Parameter func_ptr : funspec -> val ->mpred.
Axiom corable_func_ptr: forall f v, corable (func_ptr f v).

Axiom semax_call : 
  forall {Espec: OracleKind},
    forall Delta A (P Q: A -> environ -> mpred) (x: A) (F: environ -> mpred) ret argsig retsig a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax Espec Delta
          (local (tc_expr Delta a) && local (tc_exprlist Delta (snd (split argsig)) bl)  && 
         (`(func_ptr (mk_funspec  (argsig,retsig) A P Q)) (eval_expr a) &&   
          (F * `(P x) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert  
          (EX old:val, substopt ret (`old) F * maybe_retval (Q x) retsig ret)).

Axiom  semax_return :
  forall {Espec: OracleKind},
   forall Delta (R: ret_assert) ret ,
      @semax Espec Delta  
                (local (tc_expropt Delta ret (ret_type Delta)) &&
                `(R EK_return : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R.

Axiom semax_fun_id:
  forall {Espec: OracleKind},
      forall id f Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_types Delta) ! id = Some (Global_func f) ->
    @semax Espec Delta (P && `(func_ptr f) (eval_var id (globtype (Global_func f))))
                  c Q ->
    @semax Espec Delta P c Q.

(* THESE RULES FROM semax_straight *)

Axiom semax_set : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) (P: environ->mpred) id e,
    @semax Espec Delta 
        (|> (local (tc_expr Delta e) && 
            local (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).

Axiom semax_set_forward :
  forall {Espec: OracleKind}, 
forall (Delta: tycontext) (P: environ->mpred) id e,
    @semax Espec Delta 
        (|> (local (tc_expr Delta e) && 
            local (tc_temp_id id (typeof e) Delta e) && 
          P))
          (Sset id e) 
        (normal_ret_assert 
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).

Axiom semax_ptr_compare : 
forall {Espec: OracleKind},
forall (Delta: tycontext) P id cmp e1 e2 ty sh1 sh2,
   is_comparison cmp = true  ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax Espec Delta 
        ( |> (local (tc_expr Delta e1) &&
             local (tc_expr Delta e2)  && 
           
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1 ) * TT) && 
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2 ) * TT) && 
          P))
          (Sset id (Ebinop cmp e1 e2 ty)) 
        (normal_ret_assert 
          (EX old:val, 
                 local (`eq (eval_id id)  (subst id `old 
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                            subst id `old P)).

Axiom semax_load : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t2 (v2: environ -> val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
      local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && 
       local (`(tc_val (typeof e1)) v2) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                                          (subst id (`old) P))).

Axiom semax_cast_load : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P e1 t1 t2 (v2: environ -> val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast t1 t2 = true ->
      local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && 
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1) v2)) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1) v2))) &&
                                          (subst id (`old) P))).

Axiom semax_store:
  forall {Espec: OracleKind},
 forall Delta e1 e2 sh P,
   writable_share sh ->
   @semax Espec Delta 
          (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 (typeof e1)))  && 
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2) 
          (normal_ret_assert 
               (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).

(* THESE RULES FROM semax_lemmas *)

Axiom semax_skip:
  forall {Espec: OracleKind},
   forall Delta P, @semax Espec Delta P Sskip (normal_ret_assert P).

Axiom semax_pre_post:
  forall {Espec: OracleKind},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
   (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) &&  R' ek vl |-- R ek vl) ->
   @semax Espec Delta P' c R' -> @semax Espec Delta P c R.

(**************** END OF stuff from semax_rules ***********)

Axiom semax_frame: 
  forall {Espec: OracleKind},
  forall Delta P s R F,
   closed_wrt_modvars s F ->
  @semax Espec Delta P s R ->
    @semax Espec Delta (P * F) s (frame_ret_assert R F).

Axiom semax_extract_prop:
  forall {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q, 
           (PP -> @semax Espec Delta P c Q) -> 
           @semax Espec Delta (!!PP && P) c Q.

End CLIGHT_SEPARATION_LOGIC.
