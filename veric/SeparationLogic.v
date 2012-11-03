Require Export veric.base.
Require Export veric.Address.
Require Export msl.eq_dec.
Require Export msl.shares.
Require Export msl.seplog.
Require Export msl.alg_seplog.
Require Export msl.log_normalize.
Require Export veric.expr.
Require Import veric.juicy_extspec.
Require veric.seplog.
Require veric.assert_lemmas.
Require msl.msl_standard.

Definition mpred : Type := predicates_hered.pred veric.seplog.rmap.
Instance Nveric: NatDed mpred := algNatDed veric.seplog.rmap.
Instance Sveric: SepLog mpred := algSepLog veric.seplog.rmap.
Instance Cveric: ClassicalSep mpred := algClassicalSep veric.seplog.rmap.
Instance Iveric: Indir mpred := algIndir veric.seplog.rmap.
Instance Rveric: RecIndir mpred := algRecIndir veric.seplog.rmap.
Instance SIveric: SepIndir mpred := algSepIndir veric.seplog.rmap.
Instance SRveric: SepRec mpred := algSepRec veric.seplog.rmap.

Hint Resolve any_environ : typeclass_instances.

Definition assert := environ -> mpred.
Definition ret_assert := exitkind -> option val -> assert.

Definition VALspec_range: Z -> Share.t -> Share.t -> address -> mpred := res_predicates.VALspec_range.

Definition address_mapsto: memory_chunk -> val -> Share.t -> Share.t -> address -> mpred := 
       res_predicates.address_mapsto.

Local Open Scope logic.

Definition func_at : funspec -> address -> mpred := veric.seplog.func_at.

Bind Scope pred with assert.
Local Open Scope pred.

Definition closed_wrt_vars {B} (S: ident -> Prop) (F: environ -> B) : Prop := 
  forall rho te',  
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition local:  (environ -> Prop) -> assert :=  lift1 prop.

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

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch => 
    match v1 with
     | Vptr b ofs => 
          address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)
     | _ => FF
    end
  | _ => FF
  end. 

Definition eval_cast (t t': type) (v: val) : val := force_val (sem_cast v t t').

Definition writable_share: share -> Prop := seplog.writable_share. 

Definition writable_block (id: ident) (n: Z): assert :=
        EX v: val*type,  EX a: address, EX rsh: Share.t,
          (local(fun rho => ge_of rho id = Some v /\ val2adr (fst v) a) && lift0 (VALspec_range n rsh Share.top a)).

Fixpoint writable_blocks (bl : list (ident*Z)) : assert :=
 match bl with
  | nil => emp 
  | (b,n)::bl' => writable_block b n * writable_blocks bl'
 end.

Definition fun_assert (fml: funsig) (A: Type) (P Q: A -> assert) (v: val) : mpred :=
  res_predicates.fun_assert fml A P Q v.

Definition lvalue_block (rsh: Share.t) (e: Clight.expr) : assert :=
  fun rho => 
     match eval_lvalue e rho with 
     | Vptr b i => VALspec_range (sizeof (Clight.typeof e)) rsh Share.top (b, Int.unsigned i)
     | _ => FF
    end.

Definition var_block (rsh: Share.t) (idt: ident * type) : assert :=
         lvalue_block rsh (Clight.Evar (fst idt) (snd idt)).

Definition stackframe_of (f: Clight.function) : assert :=
  fold_right sepcon emp (map (var_block Share.top) (fn_vars f)).

Lemma  subst_extens {A}{NA: NatDed A}: 
 forall a v (P Q: environ -> A), P |-- Q -> subst a v P |-- subst a v Q.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition type_of_funsig (fsig: funsig) := Tfunction (type_of_params (fst fsig)) (snd fsig).
Definition fn_funsig (f: function) : funsig := (fn_params f, fn_return f).

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ | Tfloat _ _ => true
  | _ => false
  end.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => typecheck_vals (map (fun xt => (eval_id (fst xt) rho)) formals) (map (@snd _ _) formals) = true.

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

Definition bind_ret (vl: option val) (t: type) (Q: assert) : assert :=
     match vl, t with
     | None, Tvoid => lift1 Q (make_args nil nil)
     | Some v, _ => !! (typecheck_val v t = true) && 
                              lift1 Q (make_args (ret_temp::nil) (v::nil))
     | _, _ => FF
     end.

Definition overridePost  (Q: assert)  (R: ret_assert) := 
     fun ek vl => if eq_dec ek EK_normal then (!! (vl=None) && Q) else R ek vl.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) := 
  fun ek vl  => EX x:A, R x ek vl .

Definition normal_ret_assert (Q: assert) : ret_assert := 
   fun ek vl => !!(ek = EK_normal) && (!! (vl = None) && Q).

Definition with_ge (ge: genviron) (G: assert) : mpred :=
     G (mkEnviron ge (Map.empty _) (Map.empty _)).

Definition frame_ret_assert (R: ret_assert) (F: assert) : ret_assert := 
      fun ek vl => R ek vl * F.

Lemma normal_ret_assert_derives:
 forall P Q rho,
  P rho |-- Q rho ->
  forall ek vl, normal_ret_assert P ek vl rho |-- normal_ret_assert Q ek vl rho.
Proof.
 intros.
 unfold normal_ret_assert; intros; normalize.
 apply andp_derives.
 apply derives_refl.
 apply andp_derives.
 apply derives_refl.
 auto.
Qed.
Hint Resolve normal_ret_assert_derives.

Lemma normal_ret_assert_FF:
  forall ek vl, normal_ret_assert FF ek vl = FF.
Proof.
unfold normal_ret_assert. intros. normalize.
Qed.

Lemma frame_normal:
  forall P F, 
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (P * F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, normal_ret_assert.
normalize.
Qed.

Definition for1_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => Inv
 | EK_break => R EK_normal None
 | EK_continue => Inv
 | EK_return => R EK_return vl
 end.

Definition for2_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => Inv
 | EK_break => fun _ => FF
 | EK_continue => fun _ => FF 
 | EK_return => R EK_return vl
 end.

Lemma frame_for1:
  forall Q R F, 
   frame_ret_assert (for1_ret_assert Q R) F = 
   for1_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, for1_ret_assert.
destruct ek; normalize.
Qed.

Lemma frame_for2:
  forall Q R F, 
   frame_ret_assert (for2_ret_assert Q R) F = 
   for2_ret_assert (Q * F) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl.
unfold frame_ret_assert, for2_ret_assert.
destruct ek; normalize.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
extensionality ek vl.
if_tac; normalize.
subst ek.
apply pred_ext; normalize.
apply pred_ext; normalize.
Qed.

Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_for2 
                 overridePost_normal: normalize.

Definition function_body_ret_assert (ret: type) (Q: assert) : ret_assert := 
   fun (ek : exitkind) (vl : option val) =>
     match ek with
     | EK_return => bind_ret vl ret Q
     | _ => FF
     end.

Definition tc_environ (Delta: tycontext) : environ -> Prop :=
   fun rho => typecheck_environ rho Delta = true.

Definition tc_temp (Delta: tycontext) (id: ident) (t: type) : Prop := 
      typecheck_temp_id id t Delta = true.

Definition tc_expr (Delta: tycontext) (e: expr) : environ -> Prop := 
    denote_tc_assert (typecheck_expr Delta e).

Definition tc_exprlist (Delta: tycontext) (e: list expr)  : environ -> Prop := 
      denote_tc_assert (typecheck_exprlist Delta e).

Definition tc_lvalue (Delta: tycontext) (e: expr) : environ -> Prop := 
     denote_tc_assert (typecheck_lvalue Delta e).

Lemma extend_local: forall P, extensible (local P).
Proof.
intros. intro; intros.
intros w [? [? [? [? ?]]]].
unfold local in *.
apply H0.
Qed.

Lemma corable_fun_assert: forall fsig A Pre Post v, corable (fun_assert fsig A Pre Post v).
Proof.
intros. unfold corable.
intros.
simpl.
apply normalize.corable_andp_sepcon1.
apply assert_lemmas.corable_fun_assert.
Qed.

Fixpoint arglist (n: positive) (tl: typelist) : list (ident*type) :=
 match tl with 
  | Tnil => nil
  | Tcons t tl' => (n,t):: arglist (n+1)%positive tl'
 end.

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Definition exit_tycon (c: statement) (Delta: tycontext) (ek: exitkind) : tycontext :=
  match ek with 
  | EK_normal => update_tycon Delta c 
  | _ => Delta 
  end.

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , Genv.init_data_list_size (gvar_init l)) end.

Definition main_pre (prog: program) : unit -> assert :=
(fun tt _ => writable_blocks (map (initblocksize type) prog.(prog_vars)) 
                             (empty_environ (Genv.globalenv prog))).

Definition main_post (prog: program) : unit -> assert := 
  (fun tt => TT).

Definition match_globvars (gvs: list (ident * globvar type)) (V: varspecs) :=
  forall id t, In (id,t) V -> exists g: globvar type, gvar_info g = t /\ In (id,g) gvs.

Global Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.

(* Don't know why this next Hint doesn't work unless fully instantiated;
   perhaps because one needs both "contractive" and "typeclass_instances"
   Hint databases if this next line is not added. *)
Hint Resolve (@subp_sepcon mpred Nveric Iveric Sveric SIveric Rveric SRveric): contractive.

Module Type EXTERNAL_SPEC.
  Parameter Z:Type.
  Parameter Hspec : juicy_ext_spec Z.
End EXTERNAL_SPEC.

Module Type  CLIGHT_SEPARATION_LOGIC.

Local Open Scope pred.

Declare Module ExtSpec: EXTERNAL_SPEC.

Parameter semax:  tycontext -> assert -> statement -> ret_assert -> Prop.

(***************** SEMAX_LEMMAS ****************)

Axiom extract_exists:
  forall (A : Type)  (P : A -> assert) c (Delta: tycontext) (R: A -> ret_assert),
  (forall x, semax Delta (P x) c (R x)) ->
   semax Delta (EX x:A, P x) c (existential_ret_assert R).

(** THESE RULES FROM semax_prog **)

Definition semax_body
       (V: varspecs) (G: funspecs) (f: function) (spec: ident * funspec) : Prop :=
  match spec with (_, mk_funspec _ A P Q) =>
    forall x,
      semax (func_tycontext f V G)
          ((local (tc_formals (fn_params f)) && P x) *  stackframe_of f)
          f.(fn_body)
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f))
 end.

Parameter semax_func: forall (V: varspecs) (G: funspecs) (fdecs: list (ident * fundef)) (G1: funspecs), Prop.

Definition semax_prog 
     (prog: program) (V: varspecs) (G: funspecs) : Prop :=
  compute_list_norepet (map (@fst _ _) prog.(prog_funct)
                                       ++ map (@fst _ _) prog.(prog_vars)) = true /\
  semax_func V G (prog.(prog_funct)) G /\
   match_globvars (prog.(prog_vars)) V /\
    In (prog.(prog_main), mk_funspec (nil,Tvoid) unit (main_pre prog ) (main_post prog)) G.

Axiom semax_func_nil: forall V G, semax_func V G nil nil.

Definition semax_body_params_ok f : bool :=
   andb 
        (compute_list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)))
        (compute_list_norepet (map (@fst _ _) (fn_vars f))).

Axiom semax_func_cons: forall fs id f A P Q (V: varspecs)  (G G': funspecs),
      andb (id_in_list id (map (@fst _ _) G)) 
      (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
        (semax_body_params_ok f)) = true ->
      semax_body V G f (id, mk_funspec (fn_funsig f) A P Q ) ->
      semax_func V G fs G' ->
      semax_func V G ((id, Internal f)::fs) 
           ((id, mk_funspec (fn_funsig f) A P Q ) :: G').

Parameter semax_external:
  forall (ef: external_function) (A: Type) (P Q: A -> assert),  Prop.


Axiom semax_func_cons_ext: 
   forall (V: varspecs) (G: funspecs) fs id ef fsig A P Q (G': funspecs),
      andb (id_in_list id (map (@fst _ _) G))
              (negb (id_in_list id (map (@fst _ _) fs))) = true ->
      semax_external ef A P Q ->
      semax_func V G fs G' ->
      semax_func V G ((id, External ef (fst fsig) (snd fsig))::fs) 
           ((id, mk_funspec (arglist 1%positive (fst fsig), (snd fsig)) A P Q)  :: G').

Definition main_params (ge: genv) start : Prop :=
  exists b, exists func,
    Genv.find_symbol ge start = Some b /\
        Genv.find_funct ge (Vptr b Int.zero) = Some (Internal func) /\
        func.(fn_params) = nil.

(* THESE RULES FROM semax_loop *)

Axiom semax_ifthenelse : 
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Delta (P && local (lift1 (typed_true (typeof b)) (eval_expr b))) c R -> 
     semax Delta (P && local (lift1 (typed_false (typeof b)) (eval_expr b))) d R -> 
     semax Delta (local (tc_expr Delta b) && P) (Sifthenelse b c d) R.

Axiom semax_seq:
forall Delta R P Q h t, 
    semax Delta P h (overridePost Q R) -> 
    semax (update_tycon Delta h) Q t R -> 
    semax Delta P (Ssequence h t) R.

Axiom seq_assoc:  
   forall Delta P s1 s2 s3 R,
        semax Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        semax Delta P (Ssequence (Ssequence s1 s2) s3) R.

Axiom semax_for : 
forall Delta Q Q' test incr body R,
     bool_type (typeof test) = true ->
     Q  |-- local (tc_expr Delta test) ->
     (local (lift1 (typed_false (typeof test)) (eval_expr test)) && Q |-- R EK_normal None) ->
     semax Delta (local (lift1 (typed_true (typeof test)) (eval_expr test)) && Q) body (for1_ret_assert Q' R) ->
     semax Delta Q' incr (for2_ret_assert Q R) ->
     semax Delta Q (Sfor' test incr body) R.

Axiom semax_while : 
forall Delta Q test body R,
     bool_type (typeof test) = true ->
     (Q |-- local (tc_expr Delta test)) ->
     (local (lift1 (typed_false (typeof test)) (eval_expr test)) && Q |-- R EK_normal None) ->
     semax Delta (local (lift1 (typed_true (typeof test)) (eval_expr test)) && Q)  body (for1_ret_assert Q R) ->
     semax Delta Q (Swhile test body) R.

(* THESE RULES FROM semax_call *)

Axiom semax_call : 
    forall Delta A (P Q: A -> assert) x F ret fsig a bl,
           match_fsig fsig bl ret = true ->
  semax Delta
          (local (tc_expr Delta a) && local (tc_exprlist Delta bl)  && 
         (lift1 (fun_assert  fsig A P Q) (eval_expr a) && 
          (F * lift1 (P x) (make_args' fsig (eval_exprlist bl)))))
         (Scall ret a bl)
         (normal_ret_assert 
          (EX old:val, substopt ret (lift0 old) F * lift1 (Q x) (get_result ret))).

Axiom  semax_return :
   forall Delta R ret ,
      semax Delta  
                (lift2 (R EK_return) (eval_expropt ret) id)
                (Sreturn ret)
                R.

Axiom semax_fun_id:
      forall id fsig (A : Type) (P' Q' : A -> assert) Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_types Delta) ! id = Some (Global_func (mk_funspec fsig A P' Q')) ->
    semax Delta (P && lift1 (fun_assert  fsig A P' Q') (eval_lvalue (Evar id (type_of_funsig fsig)))) c Q ->
    semax Delta P c Q.

Axiom semax_call_ext:
     forall Delta P Q ret a bl a' bl',
      typeof a = typeof a' ->
       local (tc_environ Delta) && P |-- 
                  local (lift2 eq (eval_expr a) (eval_expr a')) &&
                  local (lift2 eq (eval_exprlist bl) (eval_exprlist bl')) ->
  semax Delta P (Scall ret a bl) Q ->
  semax Delta P (Scall ret a' bl') Q.

(* THESE RULES FROM semax_straight *)

Axiom semax_set : 
forall (Delta: tycontext) (P: assert) id e,
    tc_temp Delta id (typeof e) ->
    semax Delta 
        (|> (local (tc_expr Delta e) && subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).

Axiom semax_set_forward : 
forall (Delta: tycontext) (P: assert) id e,
    tc_temp Delta id (typeof e) ->
    semax Delta 
        (|> (local (tc_expr Delta e) && P))
          (Sset id e) 
        (normal_ret_assert 
          (EX old:val, local (lift2 eq (eval_id id) (subst id (lift0 old) (eval_expr e))) &&
                            subst id (lift0 old) P)).

Axiom semax_load : 
forall (Delta: tycontext) sh id P e1 v2,
    tc_temp Delta id (typeof e1) ->
    semax Delta 
       (|> (local (tc_lvalue Delta e1)  && (lift2 (mapsto sh (typeof e1)) (eval_lvalue e1) v2 * P)))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (lift2 eq (eval_id id) (subst id (lift0 old) v2)) &&
                                          (subst id (lift0 old) (lift2 (mapsto sh (typeof e1)) (eval_lvalue e1) v2 * P)))).

Axiom semax_store:
 forall Delta e1 e2 v sh P,
   typecheck_store e1 -> 
   writable_share sh ->
   semax Delta 
          (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 (typeof e1)))  && 
             (lift2 (mapsto sh (typeof e1)) (eval_lvalue e1) v * P)))
          (Sassign e1 e2) 
          (normal_ret_assert 
               (lift2 (mapsto sh (typeof e1)) (eval_lvalue e1) (lift1 (eval_cast (typeof e2) (typeof e1)) (eval_expr e2)) * P)).

(* THESE RULES FROM semax_lemmas *)

Axiom semax_skip:
   forall Delta P, semax Delta P Sskip (normal_ret_assert P).

Axiom semax_pre_post:
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
   (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) &&  R' ek vl |-- R ek vl) ->
   semax Delta P' c R' -> semax Delta P c R.

(**************** END OF stuff from semax_rules ***********)

Axiom semax_frame:  forall Delta P s R F,
   closed_wrt_modvars s F ->
  semax Delta P s R ->
    semax Delta (P * F) s (frame_ret_assert R F).

Axiom semax_extract_prop:
  forall Delta (PP: Prop) P c Q, 
           (PP -> semax Delta P c Q) -> 
           semax Delta (!!PP && P) c Q.

End CLIGHT_SEPARATION_LOGIC.
