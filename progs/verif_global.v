Require Import VST.floyd.proofauto.
Require Import VST.progs.global.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition h_spec :=
 DECLARE _h
  WITH gv: globals
  PRE [  ]
          PROP  ()
          LOCAL (gvars gv)
          SEP   (data_at Ews tint (Vint (Int.repr 7)) (gv _g))
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr 7)))
           SEP (data_at Ews tint (Vint (Int.repr 7)) (gv _g)).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog [] gv
  POST [ tint ] main_post prog [] gv.

Definition Gprog : funspecs :=
        ltac:(with_library prog [h_spec; main_spec]).

Lemma body_h: semax_body Vprog Gprog f_h h_spec.
Proof.
start_function.
forward.  (* x = g; *)
forward.  (* return x; *)
Qed.

Ltac start_function1 :=
 match goal with |- semax_body _ _ ?F ?spec =>
   let D := constr:(type_of_function F) in 
   let S := constr:(type_of_funspec (snd spec)) in
   let D := eval hnf in D in let D := eval simpl in D in 
   let S := eval hnf in S in let S := eval simpl in S in 
   tryif (unify D S) then idtac else
   tryif function_types_compatible D S 
   then idtac "Warning: the function-body parameter/return types are not identical to the funspec types, although they are compatible:
Function body:" D "
Function spec:" S
   else
   (fail "Function signature (param types, return type) from function-body does not match function signature from funspec
Function body: " D "
Function spec: " S)
 end;
 match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH _: globals
               PRE  [] main_pre _ nil _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (NDmk_funspec _ _ _ ?Pre _)) =>
   match Pre with
   | (fun x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end.


Ltac process_one_globvar :=
 first
  [ simple eapply process_globvar_space;
    [simpl; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | simpl; computable | ]
  | simple eapply process_globvar';
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | compute; congruence | ]
  | fail; (* admitted *)
    simple eapply process_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I
      | compute; clear; congruence
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence |  ]
  | fail; (* admitted *)
    simple eapply process_globvar_star';
        [reflexivity | reflexivity | reflexivity
        | reflexivity | compute; split; clear; congruence
       | simpl gvar_info; simpl gvar_readonly; simpl readonly2share;
         change (Share.lub extern_retainer Tsh) with Ews
         ]
  ];
  change (Share.lub extern_retainer _) with Ews;
  change (Share.lub extern_retainer _) with Ers;
  change (Vint oo _) with (Vint oo id);
  fold_types;
  rewrite ?Combinators.compose_id_right.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function1.
 rewrite main_pre_start; unfold prog_vars, prog_vars'; simpl globvars2pred.
process_one_globvar.
process_one_globvar.

Definition globvar2pred' (gv : globals) (i : ident) (v: globvar type) :=
if gvar_volatile v
then lift0 TT
else
 init_data_list2pred (gvar_init v) (readonly2share (gvar_readonly v))
   (offset_val 0 (gv i)).

Lemma one_globvar2pred: forall gv i v vl,
  gvar_volatile v = false ->
  globvars2pred gv ((i,v)::vl) = 
    (local (`(eq gv) globals_of_env) &&
    (init_data_list2pred (gvar_init v) (readonly2share (gvar_readonly v))
              (offset_val 0 (gv i))))
     * globvars2pred gv vl.
Proof.
intros.
unfold globvars2pred; fold globvars2pred.
extensionality rho.
unfold_lift.
unfold local, lift1, lift2.
simpl.
unfold globvar2pred at 1.
simpl. rewrite H.
apply pred_ext; normalize.
rewrite prop_true_andp by auto.
rewrite !offset_zero_globals_of_env; auto.
rewrite !offset_zero_globals_of_env; auto.
Qed.

rewrite one_globvar2pred by reflexivity.
match goal with |- semax ?D (?P1 * (?P2 * ?P3) * ?P4) ?C ?Q =>
   pose (CTX x := semax D (P1 * (x * P3) * P4) C Q);
   change (CTX P2)
end.
clearbody CTX.

set (sh :=  readonly2share (gvar_readonly _)).
simpl gvar_init.

change (init_data_list2pred (?A::?B) ?sh ?v) 
    with (init_data2pred A (Share.lub extern_retainer sh) v * init_data_list2pred B sh (offset_val (init_data_size A) v));
cbv beta;
rewrite ?offset_offset_val;
simpl Z.add.

Lemma init_data2pred_rejigger:
  forall {cs : compspecs} (Delta : tycontext) (idata : init_data) 
    (rho : environ) (sh : Share.t) (b : block) (ofs : Z) (v : val),
  tc_environ Delta rho ->
  v = Vptr b (Ptrofs.repr 0) ->
  readable_share sh ->
  init_data2pred idata sh (offset_val ofs v) rho
  |-- init_data2pred' Delta (globals_of_env rho) idata sh (offset_val ofs v) rho.


Search init_data2pred.
unfold init_data2pred.


change (init_data_list2pred (?A::?B) ?sh ?v) 
    with (init_data2pred A (Share.lub extern_retainer sh) v * init_data_list2pred B sh (offset_val (init_data_size A) v));
simpl init_data_size;
rewrite ?offset_offset_val;
simpl Z.add.

change (init_data_list2pred (?A::?B) ?sh ?v) 
    with (init_data2pred A (Share.lub extern_retainer sh) v * init_data_list2pred B sh (offset_val (init_data_size A) v));
simpl init_data_size;
rewrite offset_offset_val;
simpl Z.add.

match goal 

unfold gvar_init.
unfold init_data_list2pred.

; cbv beta zeta.
simpl.
unfold globals_of_env.
unfold gvar_volatile; cbv iota. simpl fst; simpl snd.



simpl gvar_init.



match goal with |- context [initdatalist2pred (?A::?B)] =>
  change (initdatalist2pred (?A::?B) ?sh ?v) with (initdat2pred A 
simpl.
Locate mapsto_.
unfold init_data
simpl.


unfold init_data_list2pred.



normalize.
Definition globvars2pred  (gv: globals)  (vl: list (ident * globvar type)) : environ->mpred :=
  (lift2 andp) (fun rho => prop (gv = globals_of_env rho))
  (fold_right sepcon emp (map (globvar2pred gv) vl)).

Search globvars2pred.

simple eapply process_globvar_array;
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | apply Coq.Init.Logic.I
      | compute; clear; congruence
      | repeat eapply map_instantiate; symmetry; apply map_nil
      | compute; split; clear; congruence |  ].

process_one_globvar.


process_idstar.



rewrite data_at_tuint_tint.
forward_call gv.
forward.
Qed.


