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
Require msl.msl_standard.
Definition const {A B} (a : A) := fun _ : B => a.

Definition mpred : Type := predicates_hered.pred veric.seplog.rmap.
Instance Nveric: NatDed mpred := algNatDed veric.seplog.rmap.
Instance Sveric: SepLog mpred := algSepLog veric.seplog.rmap.
Instance Cveric: ClassicalSep mpred := algClassicalSep veric.seplog.rmap.
Instance Iveric: Indir mpred := algIndir veric.seplog.rmap.
Instance Rveric: RecIndir mpred := algRecIndir veric.seplog.rmap.
Instance SIveric: SepIndir mpred := algSepIndir veric.seplog.rmap.

Definition any_environ : environ.
Admitted.

Hint Resolve any_environ : typeclass_instances.

Definition assert := environ -> mpred.
Definition ret_assert := exitkind -> list val -> assert.

Definition VALspec_range: Z -> Share.t -> Share.t -> address -> mpred := res_predicates.VALspec_range.

Definition address_mapsto: memory_chunk -> val -> Share.t -> Share.t -> address -> mpred := 
       res_predicates.address_mapsto.

Local Open Scope logic.

Definition func_at : funspec -> address -> mpred := veric.seplog.func_at.

Bind Scope pred with assert.
Local Open Scope pred.

Definition closed_wrt_vars (S: ident -> Prop) (F: assert) : Prop := 
  forall rho te',  
     (forall i, S i \/ PTree.get i (te_of rho) = PTree.get i te') ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition expr_true (e: Clight.expr): assert := 
  fun rho => !! (bool_val (eval_expr rho e) (Clight.typeof e) = Some true).

Definition subst (x: ident) (v: val) (P: assert) : assert :=
   fun s => P (env_set s x v).

Definition mapsto' (sh: Share.t) (e1: Clight.expr) (v2 : val): assert :=
 fun rho => 
  match access_mode (Clight.typeof e1) with
  | By_value ch => 
    match eval_lvalue rho e1 with
     | Vptr b ofs => 
          address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)
     | _ => FF
    end
  | _ => FF
  end. 

Definition writable_block (id: ident) (n: Z): assert :=
   fun rho => 
        EX v: val*type,  EX a: address, EX rsh: Share.t,
          !! (ge_of rho id = Some v /\ val2adr (fst v) a) && VALspec_range n rsh Share.top a.

Fixpoint writable_blocks (bl : list (ident*Z)) : assert :=
 match bl with
  | nil => emp 
  | (b,n)::bl' => writable_block b n * writable_blocks bl'
 end.

Definition fun_assert: 
  forall  (v: val) (fml: funsig) (A: Type) (P Q: A -> list val -> mpred), mpred :=
  res_predicates.fun_assert.

Definition lvalue_block (rsh: Share.t) (e: Clight.expr) : assert :=
  fun rho => 
     match eval_lvalue rho e with 
     | Vptr b i => VALspec_range (sizeof (Clight.typeof e)) rsh Share.top (b, Int.unsigned i)
     | _ => FF
    end.

Definition var_block (rsh: Share.t) (idt: ident * type) : assert :=
         lvalue_block rsh (Clight.Evar (fst idt) (snd idt)).

Definition stackframe_of (f: Clight.function) : assert :=
  fold_right sepcon emp (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

Lemma  subst_extens: 
 forall a v P Q, P |-- Q -> subst a v P |-- subst a v Q.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition bind_args (formals: list (ident * type)) (P: list val -> mpred) : assert :=
   fun rho => let vl := map (fun xt => (eval_expr rho (Etempvar (fst xt) (snd xt)))) formals
          in !! (typecheck_vals vl (map (@snd _ _) formals) = true) && P vl.

Definition bind_ret (vl: list val) (t: type) (Q: list val -> mpred) : mpred :=
     match vl, t with
     | nil, Tvoid => Q nil
     | v::nil, _ => !! (typecheck_val v t = true) && Q (v::nil)  
     | _, _ => FF
     end.

Definition overridePost  (Q: assert)  (R: ret_assert) := 
     fun ek vl => if eq_dec ek EK_normal then (!! (vl=nil) && Q) else R ek vl.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) := 
  fun ek vl  => EX x:A, R x ek vl .

Definition normal_ret_assert (Q: assert) : ret_assert := 
   fun ek vl => !!(ek = EK_normal) && (!! (vl = nil) && Q).

Definition with_ge (ge: genviron) (G: assert) : mpred :=
     G (mkEnviron ge (Maps.PTree.empty _) (Maps.PTree.empty _)).

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
 | EK_break => R EK_normal nil
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

Definition function_body_ret_assert (ret: type) (Q: list val -> mpred) : ret_assert := 
   fun (ek : exitkind) (vl : list val) =>
     match ek with
     | EK_return => fun rho => bind_ret vl ret Q 
     | _ => FF
     end.

Definition tc_temp (Delta: tycontext) (id: ident) (t: type) : assert :=
  fun rho => !! (typecheck_temp_id id t Delta = true).

Definition tc_expr (Delta: tycontext) (e: expr) : assert:= 
  fun rho => !! denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist (Delta: tycontext) (e: list expr) : assert := 
      fun rho => !! denote_tc_assert (typecheck_exprlist Delta e) rho.

Definition tc_lvalue (Delta: tycontext) (e: expr) : assert := 
     fun rho => !! denote_tc_assert (typecheck_lvalue Delta e) rho.

Lemma extend_tc_expr: forall Delta e rho, extensible (tc_expr Delta e rho).
Admitted.
Lemma extend_tc_exprlist: forall Delta e rho, extensible (tc_exprlist Delta e rho).
Admitted.
Lemma extend_tc_lvalue: forall Delta e rho, extensible (tc_lvalue Delta e rho).
Admitted.

Global Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric. 

(* Don't know why this next Hint doesn't work unless fully instantiated... *)
Hint Resolve (@sub_sepcon mpred Nveric Iveric Sveric SIveric): contractive.

Module Type EXTERNAL_SPEC.
  Parameter Z:Type.
  Parameter Hspec : juicy_ext_spec Z.
End EXTERNAL_SPEC.

Module Type  CLIGHT_SEPARATION_LOGIC.

Local Open Scope pred.

Declare Module ExtSpec: EXTERNAL_SPEC.

Parameter semax:  tycontext -> funspecs -> assert -> statement -> ret_assert -> Prop.

(***************** SEMAX_LEMMAS ****************)

Axiom extract_exists:
  forall (A : Type) (any: A)   (* must demonstrate that A is inhabited *)
   (P : A -> assert) c (Delta: tycontext) G (R: A -> ret_assert),
  (forall x, semax Delta G (P x) c (R x)) ->
   semax Delta G (EX x:A, P x) c (existential_ret_assert R).

(************** INITIAL WORLD *****************)

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , Genv.init_data_list_size (gvar_init l)) end.

(************ SEMAX_RULES *****************)

(** THESE RULES FROM semax_prog **)

Definition semax_body
       (G: funspecs) (f: function) (A: Type) (P Q: A -> list val -> mpred) : Prop :=
  forall x,
      semax (func_tycontext f) G
          (bind_args (fn_params f) (P x) *  stackframe_of f)
          f.(fn_body)
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x)) (stackframe_of f)).

Parameter semax_func: forall (G: funspecs) (fdecs: list (ident * fundef)) (G1: funspecs), Prop.

Definition main_pre (prog: program) : unit -> list val -> mpred :=
(fun tt vl => writable_blocks (map (initblocksize type) prog.(prog_vars)) 
                             (empty_environ (Genv.globalenv prog))).

Definition main_post (prog: program) : unit -> list val -> mpred := 
  (fun tt vl => !! (vl=nil)).

Definition semax_prog 
     (prog: program) (G: funspecs) : Prop :=
  compute_list_norepet (map (@fst _ _) prog.(prog_funct)
                                       ++ map (@fst _ _) prog.(prog_vars)) = true /\
  semax_func G (prog.(prog_funct)) G /\
    In (prog.(prog_main), mk_funspec (Tnil,Tvoid) unit (main_pre prog ) (main_post prog)) G.

Axiom semax_func_nil: forall G, semax_func G nil nil.

Definition fn_funsig (f: function) : funsig :=
 (type_of_params (fn_params f), fn_return f).

Definition semax_body_params_ok f : bool :=
   andb 
        (compute_list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)))
        (compute_list_norepet (map (@fst _ _) (fn_vars f))).

Axiom semax_func_cons: forall fs id f A P Q (G G': funspecs),
      andb (id_in_list id (map (@fst _ _) G)) 
      (andb (negb (id_in_list id (map (@fst ident fundef) fs)))
        (semax_body_params_ok f)) = true ->
      semax_body G f A P Q ->
      semax_func G fs G' ->
      semax_func G ((id, Internal f)::fs) 
           ((id, mk_funspec (fn_funsig f) A P Q ) :: G').

Parameter semax_external:
  forall (ef: external_function) (A: Type) (P Q: A -> list val -> mpred),  Prop.

Axiom semax_func_cons_ext: 
   forall (G: funspecs) fs id ef fsig A P Q (G': funspecs),
      andb (id_in_list id (map (@fst _ _) G))
              (negb (id_in_list id (map (@fst _ _) fs))) = true ->
      semax_external ef A P Q ->
      semax_func G fs G' ->
      semax_func G ((id, External ef (fst fsig) (snd fsig))::fs) 
           ((id, mk_funspec fsig A P Q)  :: G').

Definition main_params (ge: genv) start : Prop :=
  exists b, exists func,
    Genv.find_symbol ge start = Some b /\
        Genv.find_funct ge (Vptr b Int.zero) = Some (Internal func) /\
        func.(fn_params) = nil.

(* THESE RULES FROM semax_loop *)

Axiom semax_seq:
forall Delta G R P Q h t, 
    semax Delta G P h (overridePost Q R) -> 
    semax (update_tycon Delta h) G Q t R -> 
    semax Delta G P (Ssequence h t) R.

Axiom seq_assoc:  
   forall Delta G P s1 s2 s3 R,
        semax Delta G P (Ssequence s1 (Ssequence s2 s3)) R <->
        semax Delta G P (Ssequence (Ssequence s1 s2) s3) R.

Definition Cnot (e: expr) : expr :=
   Eunop Onotbool e type_bool.

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ | Tfloat _ _ => true
  | _ => false
  end.

Axiom semax_for : 
forall Delta G Q Q' test incr body R
     (TC: Q  |-- tc_expr Delta test)
     (BT: bool_type (typeof test) = true) 
     (POST: expr_true (Cnot test) && Q |-- R EK_normal nil),
     semax Delta G (expr_true test && Q) body (for1_ret_assert Q' R) ->
     semax Delta G Q' incr (for2_ret_assert Q R) ->
     semax Delta G Q (Sfor' test incr body) R.

Axiom semax_while : 
forall Delta G Q test body R
     (TC: Q |-- tc_expr Delta test)
     (BT: bool_type (typeof test) = true) 
     (POST: expr_true (Cnot test) && Q |-- R EK_normal nil),
     semax Delta G (expr_true test && Q)  body (for1_ret_assert Q R) ->
     semax Delta G Q (Swhile test body) R.

(* THESE RULES FROM seplog_soundness *)

Definition get_result (ret: option ident) (ty: type) (rho: environ) : list val :=
 match ret with None => nil | Some x => (force_val (PTree.get x (te_of rho)))::nil end.

Axiom semax_call : 
forall Delta G A (P Q: A -> list val -> mpred) x F ret fsig a bl,
      match_fsig fsig bl ret = true ->
       semax Delta G
         (tc_expr Delta a && tc_exprlist Delta bl  && 
         ((fun rho => fun_assert  (eval_expr rho a) fsig A P Q) && 
          (const F * (fun rho => P x (eval_exprlist rho bl)) )))
         (Scall ret a bl)
         (normal_ret_assert (const F * (fun rho => Q x (get_result ret (snd fsig) rho)))).

Axiom  semax_return :
   forall Delta G R ret ,
      semax Delta G 
                (fun rho => R EK_return (eval_exprlist rho (opt2list ret)) rho)
                (Sreturn ret)
                R.

Axiom semax_fun_id:
      forall id fsig (A : Type) (P' Q' : A -> list val -> mpred)
              Delta (G : funspecs) P Q c,
    In (id, mk_funspec fsig A P' Q') G ->
       semax Delta G (P && fun rho => fun_assert (eval_lvalue rho (Evar id (Tfunction (fst fsig) (snd fsig)))) fsig A P' Q')
                              c Q ->
       semax Delta G P c Q.

Axiom semax_call_ext:
     forall Delta G P Q ret a bl a' bl',
      typeof a = typeof a' ->
      (forall rho, typecheck_environ rho Delta = true ->
                        P rho |-- !! (eval_expr rho a = eval_expr rho a' /\
                                           eval_exprlist rho bl = eval_exprlist rho bl')) ->
  semax Delta G P (Scall ret a bl) Q ->
  semax Delta G P (Scall ret a' bl') Q.

Axiom semax_set : 
forall (Delta: tycontext) (G: funspecs) (P: assert) id e,
    semax Delta G 
        (tc_temp Delta id (typeof e) && tc_expr Delta e && 
           (|> fun rho => subst id (eval_expr rho e) P rho))
          (Sset id e) (normal_ret_assert P).

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Axiom semax_load : 
forall (Delta: tycontext) (G: funspecs) sh id P e1 v2,
    lvalue_closed_wrt_vars (eq id) e1 ->
    semax Delta G 
       (tc_temp Delta id (typeof e1)  && tc_lvalue Delta e1  && 
          |> (mapsto' sh e1 v2 * subst id v2 P))
       (Sset id e1)
       (normal_ret_assert (mapsto' sh e1 v2 * P)).

Axiom semax_store:
 forall Delta G e1 e2 v3 rsh P 
   (TC: typecheck_store e1 e2),
    typeof e1 = typeof e2 -> 
    
    (*!!denote_tc_assert(isCastResultType (typeof e2) (typeof e1) (typeof e1) e2) rho something along these lines*)
    (* admit:  make this more accepting of implicit conversions! *) 
   semax Delta G 
          (tc_lvalue Delta e1 && tc_expr Delta e2  && 
          |> (mapsto' (Share.splice rsh Share.top) e1 v3 * P))
          (Sassign e1 e2) 
          (normal_ret_assert (fun rho => mapsto' (Share.splice rsh Share.top) e1 (eval_expr rho e2) rho * P rho)).

Axiom semax_ifthenelse : 
   forall Delta G P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Delta G (P && expr_true b) c R -> 
     semax Delta G (P && expr_true (Cnot b)) d R -> 
     semax Delta G (tc_expr Delta b && P) (Sifthenelse b c d) R.

(* THESE RULES FROM semax_lemmas *)

Axiom semax_Sskip:
   forall Delta G P, semax Delta G P Sskip (normal_ret_assert P).

Axiom semax_pre_post:
 forall P' (R': ret_assert) Delta G P c (R: ret_assert) ,
   (forall rho,  typecheck_environ rho Delta = true ->    P rho |-- P' rho) ->
   (R' |-- R) ->
   semax Delta G P' c R' -> semax Delta G P c R.

(**************** END OF stuff from semax_rules ***********)

Axiom frame_left:  forall Delta G P s R F,
   closed_wrt_modvars s F ->
  semax Delta G P s R ->
    semax Delta G (P * F) s (frame_ret_assert R F).

Axiom derives_skip:
  forall p Delta G (R: ret_assert),
      (p |-- R EK_normal nil) -> 
        semax Delta G p Sskip R.

Axiom semax_ff:
  forall Delta G c R,  
   semax Delta G FF c R.

Axiom semax_extract_prop:
  forall Delta G (PP: Prop) P c Q, 
           (PP -> semax Delta G P c Q) -> 
           semax Delta G (!!PP && P) c Q.

End CLIGHT_SEPARATION_LOGIC.
