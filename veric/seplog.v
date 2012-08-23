Require Export veric.base.
Require Export veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.res_predicates.
Require Import veric.expr.

(* THESE NEXT DEFINITIONS are inconvenient to have inside the proof
  of separation logic soundness, but are necessary to have for the 
  client of the separation logic who wants to import the separation
   logic opaquely. *)
Definition rmap := rmap.
Instance Join_rmap: Join rmap := _.
Instance Perm_rmap: @Perm_alg rmap Join_rmap := _.
Instance Sep_rmap: @Sep_alg rmap Join_rmap := _.
Instance Canc_rmap: @Canc_alg rmap Join_rmap := _.
Instance Disj_rmap: @Disj_alg rmap Join_rmap := _.
Instance ag_rmap: ageable rmap := _.
Instance Age_rmap: @Age_alg rmap Join_rmap ag_rmap := _.
Instance Cross_rmap: Cross_alg rmap := _.
Instance Trip_rmap: Trip_alg rmap := _.

(* an experiment ... 
Instance Join_environ : Join environ := Join_equiv _.
Instance Perm_environ : Perm_alg environ := _.
Instance Sep_environ : Sep_alg environ := _.
Instance Canc_environ: Canc_alg environ := _.
Instance Disj_environ: Disj_alg environ := _.

Instance ag_environ_rmap : ageable (environ * rmap) := ag_prod' environ rmap _.
Instance Age_environ_rmap : Age_alg (environ * rmap) := asa_prod' _ _ _ _ _ _.
*)
Definition core_load : memory_chunk -> address -> val -> pred rmap := core_load.

Definition VALspec_range: Z -> Share.t -> Share.t -> address -> pred rmap := VALspec_range.

Definition address_mapsto: memory_chunk -> val -> Share.t -> Share.t -> address -> pred rmap := 
       address_mapsto.

Lemma address_mapsto_exists:
  forall ch v rsh (sh: pshare) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) rsh (pshare_sh sh) loc w 
                    /\ core w = core w0.
Proof.  exact address_mapsto_exists. Qed.

Lemma address_mapsto_VALspec_range: 
  forall (ch : memory_chunk) (v : val) rsh (sh : Share.t) (l : address),
       address_mapsto ch v rsh sh l
       |-- VALspec_range (size_chunk ch) rsh sh l.
Proof.  exact address_mapsto_VALspec_range. Qed.

Open Local Scope pred.


Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig A P Q => pureat (SomeP (A::boolT::(list val)::nil) (packPQ P Q)) (FUN fsig)
  end.


Definition assert: Type := environ -> pred rmap.

Bind Scope pred with assert.
Local Open Scope pred.

Definition closed_wrt_vars (S: ident -> Prop) (F: assert) : Prop := 
  forall rho te',  
     (forall i, S i \/ PTree.get i (te_of rho) = PTree.get i te') ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition expr_true (e: Clight.expr) (rho: environ): Prop := 
  bool_val (eval_expr rho e) (Clight.typeof e) = Some true.

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
        Ex v: val*type,  Ex a: address, Ex rsh: Share.t,
          !! (ge_of rho id = Some v /\ val2adr (fst v) a) && VALspec_range n rsh Share.top a.

Fixpoint writable_blocks (bl : list (ident*Z)) : assert :=
 fun rho => 
 match bl with
  | nil => emp 
  | (b,n)::bl' => writable_block b n rho * writable_blocks bl' rho
 end.

Definition fun_assert: 
  forall  (v: val) (fml: funsig) (A: Type) (P Q: A -> list val -> pred rmap), pred rmap :=
  res_predicates.fun_assert.

Definition lvalue_block (rsh: Share.t) (e: Clight.expr) : assert :=
  fun rho => 
     match eval_lvalue rho e with 
     | Vptr b i => VALspec_range (sizeof (Clight.typeof e)) rsh Share.top (b, Int.unsigned i)
     | _ => FF
    end.

Definition var_block (rsh: Share.t) (idt: ident * type) : assert :=
         lvalue_block rsh (Clight.Evar (fst idt) (snd idt)).

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.

Definition stackframe_of (f: Clight.function) : assert :=
  fun rho => sepcon_list (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).

Lemma  subst_extens: 
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition bind_args (formals: list (ident * type)) (P: list val -> pred rmap) : assert :=
   fun rho => let vl := map (fun xt => (eval_expr rho (Etempvar (fst xt) (snd xt)))) formals
          in !! (typecheck_vals vl (map (@snd _ _) formals) = true) && P vl.

Definition bind_ret (vl: list val) (t: type) (Q: list val -> pred rmap) : pred rmap :=
     match vl, t with
     | nil, Tvoid => Q nil
     | v::nil, _ => !! (typecheck_val v t = true) && Q (v::nil)  
     | _, _ => FF
     end.

Definition funassert (G: funspecs) : assert := 
 fun rho => 
   (All  id: ident, All fs:funspec,  !! In (id,fs) G -->
              Ex v:val, Ex loc:address, 
                   !! (ge_of rho id = Some (v, type_of_funspec fs)
                                 /\ val2adr v loc) && func_at fs loc)
   && 
   (All  loc: address, All fs:funspec, func_at fs loc --> 
             Ex id:ident,Ex v:val,  !! (ge_of rho id = Some (v, type_of_funspec fs)
                                 /\ val2adr v loc) && !! In id (map (@fst _ _) G)).

(* Unfortunately, we need core_load in the interface as well as address_mapsto,
  because the converse of 'mapsto_core_load' lemma is not true.  The reason is
  that core_load could imply partial ownership of the four bytes of the word
  using different shares that don't have a common core, whereas address_mapsto
  requires the same share on all four bytes. *)

Definition ret_assert := exitkind -> list val -> assert.

Definition overridePost  (Q: assert)  (R: ret_assert) := 
     fun ek vl => if eq_dec ek EK_normal then (fun rho => !! (vl=nil) && Q rho) else R ek vl.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) := 
  fun ek vl rho => Ex x:A, R x ek vl rho.

Definition normal_ret_assert (Q: assert) : ret_assert := 
   fun ek vl rho => !!(ek = EK_normal) && (!! (vl = nil) && Q rho).

Definition with_ge (ge: genviron) (G: assert) : pred rmap :=
     G (mkEnviron ge (Maps.PTree.empty _) (Maps.PTree.empty _)).

Definition frame_ret_assert (R: ret_assert) (F: assert) : ret_assert := 
      fun ek vl rho => R ek vl rho * F rho.

Require Import msl.normalize.

Lemma normal_ret_assert_derives:
 forall P Q rho,
  P rho |-- Q rho ->
  forall ek vl, normal_ret_assert P ek vl rho |-- normal_ret_assert Q ek vl rho.
Proof.
 intros.
 unfold normal_ret_assert; intros; normalize.
Qed.
Hint Resolve normal_ret_assert_derives.

Lemma normal_ret_assert_FF:
  forall ek vl rho, normal_ret_assert (fun rho => FF) ek vl rho = FF.
Proof.
unfold normal_ret_assert. intros. normalize.
Qed.

Lemma frame_normal:
  forall P F, 
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (fun rho => P rho * F rho).
Proof.
intros.
extensionality ek vl rho.
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
   for1_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl rho.
unfold frame_ret_assert, for1_ret_assert.
destruct ek; normalize.
Qed.

Lemma frame_for2:
  forall Q R F, 
   frame_ret_assert (for2_ret_assert Q R) F = 
   for2_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl rho.
unfold frame_ret_assert, for2_ret_assert.
destruct ek; normalize.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
extensionality ek vl rho.
if_tac; normalize.
subst ek.
apply pred_ext; normalize.
apply pred_ext; normalize.
Qed.

Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_for2 
                 overridePost_normal: normalize.

Definition function_body_ret_assert (ret: type) (Q: list val -> pred rmap) : ret_assert := 
   fun (ek : exitkind) (vl : list val) rho =>
     match ek with
     | EK_return => bind_ret vl ret Q 
     | _ => FF
     end.

Definition tc_expr (Delta: tycontext) (e: expr) : assert:= 
  fun rho => !! denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist (Delta: tycontext) (e: list expr) : assert := 
      fun rho => !! denote_tc_assert (typecheck_exprlist Delta e) rho.

Definition tc_lvalue (Delta: tycontext) (e: expr) : assert := 
     fun rho => !! denote_tc_assert (typecheck_lvalue Delta e) rho.

Lemma extend_tc_expr: forall Delta e rho, boxy extendM (tc_expr Delta e rho).
Admitted.
Lemma extend_tc_exprlist: forall Delta e rho, boxy extendM (tc_exprlist Delta e rho).
Admitted.
Lemma extend_tc_lvalue: forall Delta e rho, boxy extendM (tc_lvalue Delta e rho).
Admitted.
Hint Resolve extend_tc_expr extend_tc_exprlist extend_tc_lvalue.
Hint Resolve (@extendM_refl rmap _ _ _ _ _).






