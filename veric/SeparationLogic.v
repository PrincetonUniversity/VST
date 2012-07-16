Require Import veric.base.
Require Import veric.seplog.
Require Import veric.juicy_extspec.
Require Import veric.Clight_lemmas.
Require Import veric.expr.

Opaque rmap.
Instance Join_rmap: Join rmap := _.
Instance Perm_rmap: @Perm_alg rmap Join_rmap := _.
Instance Sep_rmap: @Sep_alg rmap Join_rmap := _.
Instance Canc_rmap: @Canc_alg rmap Join_rmap := _.
Instance Disj_rmap: @Disj_alg rmap Join_rmap := _.
Instance ag_rmap: ageable rmap := _.
Instance Age_rmap: @Age_alg rmap Join_rmap ag_rmap := _.
Instance Cross_rmap: Cross_alg rmap := _.
Instance Trip_rmap: Trip_alg rmap := _.


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
   semax Delta G (fun rho => Ex x:A, P x rho) c (existential_ret_assert R).

(************** INITIAL WORLD *****************)

Definition initblocksize (V: Type)  (a: ident * globvar V)  : (ident * Z) :=
 match a with (id,l) => (id , Genv.init_data_list_size (gvar_init l)) end.

(************ SEMAX_RULES *****************)

(** THESE RULES FROM semax_prog **)

Definition function_body_entry_assert (f: function) (P: arguments -> pred rmap) (G: funspecs) : assert :=
   fun rho : environ =>
      bind_args (fn_params f) (fun vl : arguments => P vl) rho *  stackframe_of f rho.

Definition function_body_ret_assert (f: function) (Q: arguments -> pred rmap) : ret_assert := 
   fun (ek : exitkind) (vl : list val) rho =>
     match ek with
     | EK_return => stackframe_of f rho * bind_ret vl f.(fn_return) Q 
     | _ => FF
     end.

Definition semax_body
       (G: funspecs) (f: function) (A: Type) (P Q: A -> arguments -> pred rmap) : Prop :=
      (list_norepet (map (@fst _ _) (fn_params f) ++ map (@fst _ _) (fn_temps f)) /\
       list_norepet (map (@fst _ _) (fn_vars f))) /\
  forall x,
      semax (func_tycontext f) G
          (function_body_entry_assert f (P x) G)         
          f.(fn_body)
          (function_body_ret_assert f (Q x)).

Parameter semax_func: forall (G: funspecs) (fdecs: list (ident * fundef)) (G1: funspecs), Prop.

Definition main_pre (prog: program) : unit -> arguments -> pred rmap :=
(fun tt vl => writable_blocks (map (initblocksize type) prog.(prog_vars)) 
                             (empty_environ (Genv.globalenv prog))).

Definition main_post (prog: program) : unit -> arguments -> pred rmap := 
  (fun tt vl => !! (vl=nil)).

Definition semax_prog 
     (prog: program) (G: funspecs) : Prop :=
  no_dups prog.(prog_funct) prog.(prog_vars) /\
  semax_func G (prog.(prog_funct)) G /\
    In (prog.(prog_main), mk_funspec (Tnil,Tvoid) unit (main_pre prog ) (main_post prog)) G.

Axiom semax_func_nil: forall G, semax_func G nil nil.

Definition fn_funsig (f: function) : funsig :=
 (type_of_params (fn_params f), fn_return f).

Axiom semax_func_cons: forall fs id f A P Q (G G': funspecs),
      In id (map (@fst _ _) G) ->
      not (In id (map (@fst ident fundef) fs)) ->
      semax_body G f A P Q ->
      semax_func G fs G' ->
      semax_func G ((id, Internal f)::fs) 
           ((id, mk_funspec (fn_funsig f) A P Q ) :: G').

Parameter semax_external:
  forall (ef: external_function) (A: Type) (P Q: A -> arguments -> pred rmap),  Prop.

Axiom semax_func_cons_ext: 
   forall (G: funspecs) fs id ef fsig A P Q (G': funspecs),
      In id (map (@fst _ _) G) ->
      not (In id (map (@fst _ _) fs)) ->
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

Axiom semax_Sseq:
forall Delta G R P Q h t, 
    semax Delta G P h (overridePost Q R) -> 
    semax Delta G Q t R -> 
    semax Delta G P (Ssequence h t) R.

Axiom seq_assoc:  
   forall Delta G P s1 s2 s3 R,
        semax Delta G P (Ssequence s1 (Ssequence s2 s3)) R <->
        semax Delta G P (Ssequence (Ssequence s1 s2) s3) R.

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

Definition Cnot (e: Clight.expr) : Clight.expr :=
   Clight.Eunop Onotbool e type_bool.

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ | Tfloat _ _ => true
  | _ => false
  end.

Axiom semax_for : 
forall Delta G Q Q' test incr body R
     (TC_expr: typecheck_expr Delta test = true)
     (BT: bool_type (Clight.typeof test) = true) 
     (POST: forall rho,  assert_expr (Cnot test) rho && Q rho |-- R EK_normal nil rho),
     semax Delta G 
                (fun rho => assert_expr test rho && Q rho) body (for1_ret_assert Q' R) ->
     semax Delta G Q' incr (for2_ret_assert Q R) ->
     semax Delta G Q (Sfor' test incr body) R.

Axiom semax_while : 
forall Delta G Q test body R
     (TC_expr: typecheck_expr Delta test = true)
     (BT: bool_type (Clight.typeof test) = true) 
     (POST: forall rho,  assert_expr (Cnot test) rho && Q rho |-- R EK_normal nil rho),
     semax Delta G 
                (fun rho => assert_expr test rho && Q rho) body (for1_ret_assert Q R) ->
     semax Delta G Q (Swhile test body) R.

(* THESE RULES FROM seplog_soundness *)

Definition semax1 Delta G P c Q :=
  forall (R: ret_assert), R EK_normal nil = Q -> semax Delta G P c R.

Definition get_result (ret: option ident) (ty: type) (rho: environ) :=
 match ret with None => nil | Some x => (force_val (PTree.get x (te_of rho)), ty)::nil end.

Axiom semax_call_basic : 
forall Delta G A (P Q: A -> arguments -> pred rmap) x F ret fsig a bl
      (TC1: typecheck_expr Delta a = true)
      (TC2: typecheck_exprlist Delta bl = true),
       semax1 Delta G
         (fun rho => fun_assert  (eval_expr rho a) fsig A P Q && 
         (F * P x (zip_arguments (map (eval_expr rho) bl) (fst fsig))))
         (Scall ret a bl)
         (fun rho => F * Q x (get_result ret (snd fsig) rho)).

Axiom  semax_return :
   forall Delta G R ret 
      (TC: typecheck_stmt Delta (Sreturn ret) = true),
      semax Delta G 
                (fun rho => R EK_return (map (eval_expr rho) (opt2list ret)) rho)
                (Sreturn ret)
                R.

Axiom semax_fun_id:
      forall id fsig (A : Type) (P' Q' : A -> arguments -> pred rmap)
              Delta (G : funspecs) P Q c,
    In (id, mk_funspec fsig A P' Q') G ->
       semax Delta G (fun rho => P rho 
                                && fun_assert (eval_lvalue rho (Evar id (Tfunction (fst fsig) (snd fsig)))) fsig A P' Q')
                              c Q ->
       semax Delta G P c Q.

Axiom semax_call_ext:
     forall Delta G P Q ret a bl a' bl',
      typeof a = typeof a' ->
      (forall rho, typecheck_environ rho Delta = true ->
                        P rho |-- !! (eval_expr rho a = eval_expr rho a' /\
                                           map (eval_expr rho) bl = map (eval_expr rho) bl')) ->
  semax Delta G P (Scall ret a bl) Q ->
  semax Delta G P (Scall ret a' bl') Q.

Axiom semax_set : 
forall (Delta: tycontext) (G: funspecs) (P: assert) id e,
    typecheck_expr Delta (Etempvar id (typeof e)) = true ->   
    typecheck_expr Delta e = true ->
    semax1 Delta G (fun rho => |> subst id (eval_expr rho e) P rho) (Sset id e) P.

Definition closed_wrt_vars (S: ident -> Prop) (F: assert) : Prop := 
  forall rho te',  
     (forall i, S i \/ PTree.get i (te_of rho) = PTree.get i te') ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Axiom semax_load : 
forall (Delta: tycontext) (G: funspecs) sh id P e1 e2,
    typecheck_expr Delta (Etempvar id (typeof e1)) = true ->   
    typecheck_lvalue Delta e1 = true ->
    typecheck_expr Delta e2 = true ->
    closed_wrt_vars (eq id) (mapsto sh e1 e2) ->
    semax1 Delta G 
       (fun rho => |> (mapsto sh e1 e2 rho * subst id (eval_expr rho e2) P rho))
       (Sset id e1)
       (fun rho => mapsto sh e1 e2 rho * P rho).

Axiom semax_store:
 forall Delta G e1 e2 e3 rsh P,
    typecheck_lvalue Delta e1 = true ->
    typecheck_expr Delta e2 = true ->
    typeof e1 = typeof e2 ->   (* admit:  make this more accepting of implicit conversions! *) 
   semax1 Delta G (fun rho => |> (mapsto (splice rsh Share.top) e1 e3 rho * P rho))
                   (Sassign e1 e2) 
                  (fun rho => mapsto (splice rsh Share.top) e1 e2 rho * P rho).

Axiom semax_ifthenelse : 
   forall Delta G P (b: expr) c d R,
     typecheck_expr Delta b = true ->
      bool_type (typeof b) = true ->
     semax Delta G (fun rho => P rho && assert_expr b rho) c R -> 
     semax Delta G (fun rho => P rho && assert_expr (Cnot b) rho) d R -> 
     semax Delta G P (Sifthenelse b c d) R.

(* THESE RULES FROM semax_lemmas *)

Axiom semax_Sskip:
   forall Delta G P, semax1 Delta G P Sskip P.

Axiom semax_pre_post:
 forall P' (R': ret_assert) Delta G P c (R: ret_assert) ,
   (forall rho,  typecheck_environ rho Delta = true ->    P rho |-- P' rho) ->
   (forall ek vl rho, R' ek vl rho |-- R ek vl rho) ->
   semax Delta G P' c R' -> semax Delta G P c R.

(**************** END OF stuff from semax_rules ***********)

Axiom frame_left:  forall Delta G P s R F,
   closed_wrt_modvars s F ->
  semax Delta G P s R ->
    semax Delta G (fun rho => P rho * F rho) s (frame_ret_assert R F).

Axiom derives_skip:
  forall p Delta G (R: ret_assert),
      (forall rho, p rho |-- R EK_normal nil rho) -> 
        semax Delta G p Sskip R.

Axiom semax_ff:
  forall Delta G c R,  
   typecheck_stmt Delta c = true -> 
   semax Delta G (fun rho => FF) c R.

End CLIGHT_SEPARATION_LOGIC.
