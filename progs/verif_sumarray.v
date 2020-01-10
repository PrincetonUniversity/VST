Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.progs.sumarray. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Functional spec of this program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; omega.
Qed.

(* Beginning of the API spec for the sumarray.c program *)

Definition sumarray_spec : ident * Newfunspec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ _a OF (tptr tuint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed;
          Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  POST [ tuint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(* Note: It would also be reasonable to let [contents] have type [list int].
  Then the [Forall] would not be needed in the PROP part of PRE.
*)

(* The precondition of "int main(void){}" always looks like this. *)
(*Definition main_Ispec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] (gassert2assert nil (main_pre prog tt nil gv))
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (1+2+3+4)))) 
     SEP(TT).
*)

Definition main_spec: ident * Newfunspec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] (main_pre_old prog tt gv)
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (1+2+3+4)))) 
     SEP(TT).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [sumarray_spec; main_spec]).

(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)

Lemma new_elim_gclose_precondition:
  forall {CS: compspecs} {Espec: OracleKind} al Delta P F c Q,
   (*closed_wrt_vars (fun i => ~ In i al) P  ->
   closed_wrt_lvars (fun _ => True) P ->    *)
   semax Delta ((local (fun rho =>  map (Map.get (te_of rho)) al = map Some (map (fun i : ident => eval_id i rho) al)) 
                 && gassert2assert al P) 
                * F) c Q ->
   semax Delta (Clight_seplog.gclose_precondition al P * F) c Q.
Proof.
intros.
 eapply semax_pre; try eassumption.
 apply andp_left2.
 apply sepcon_derives; [ | apply derives_refl].
 apply gclose_gassert.
Qed.
(*
Check Clight_seplog.AssertTT2ArgsTT.
Lemma XX {A} P ids ts rho U: @Clight_seplog.AssertTT2ArgsTT A ids P ts rho = (Clight_seplog.assert2gassert ids U).
simpl in *. Search gassert2assert. Search Clight_seplog.AssertTT2ArgsTT.  clear ts.
unfold assert2gassert.
Check (Clight_seplog.assert2gassert ids). Check (P ts).
(U = fun Q R gv -> *)

Lemma gclose_gassert_eq {al P}: Clight_seplog.gclose_precondition al P =
      (local (fun rho => map (Map.get (te_of rho)) al = map Some (map (fun i => eval_id i rho) al)) &&
          gassert2assert al P).
Proof. apply pred_ext. apply gclose_gassert. apply gclose_gassert_inv. Qed.
(*
Parameter A : rmaps.TypeTree.
Parameter UU : (forall ts : list Type,
      functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts A) mpred
   -> environ -> mpred).

Check gfunction_body_ret_assert.
Lemma gfunction_body_ret_assert_char':
  forall (t : type) R,
  gfunction_body_ret_assert t R |--
  function_body_ret_assert t (fun rho => R (ge_of rho, nil)).
intros. (*
remember (@Clight_seplog.AssertTT2ArgsTT A [Clight_seplog.ret_temp] UU nil) as PP.
simpl in *. Locate assert2gassert.
remember (Clight_seplog.assert2gassert [Clight_seplog.ret_temp] (UU nil)). 
Abort.*)
unfold gfunction_body_ret_assert, function_body_ret_assert. f_equal.
extensionality vl. rewrite gbind_ret_char. destruct vl; trivial.
Print bind_ret.
fun rho => R (ge_of_rho, nil)
 f_equal.  gbind_ret.*)

(*
Lemma gfunction_body_ret_assert_char':
  forall (t : type) R U,
  gfunction_body_ret_assert t (@Clight_seplog.AssertTT2ArgsTT A [Clight_seplog.ret_temp] R nil) =
  function_body_ret_assert t U.
intros.
remember (@Clight_seplog.AssertTT2ArgsTT A [Clight_seplog.ret_temp] UU nil) as PP.
simpl in PP.specialize (PP UU). simpl in PP.

 
Lemma gfunction_body_ret_assert_char' {A} ts:
  forall (t : type) R U,
  gfunction_body_ret_assert t (@Clight_seplog.AssertTT2ArgsTT A [Clight_seplog.ret_temp] (R ts)) =
  U.(PROPr Q1 (RETr v (SEPr Q3))) =
  function_body_ret_assert t (PROPx Q1 LOCAL (temp ret_temp v)  (SEPx Q3))*)

Ltac start_function1 :=
 leaf_function;
 match goal with |- semax_body ?V ?G ?F ?spec =>
    check_normalized F;
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_Newfunspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_Newfunspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ _ nil _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec; simpl map;

 match goal with
   |- semax_body _ _ _ (pair _ (mk_Newfunspec _ _ _ (Clight_seplog.AssertTT2ArgsTT ?ids ?Pre) _ _ _)) =>
   split3; [check_parameter_types' | check_return_type | ];
   match Pre with
   (*| (fun _ x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]*)
   | (fun _ i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end; 
 eapply semax_pre.

Ltac start_function2 :=
 try match goal with |- semax _ (fun rho => ?A rho * ?B rho) _ _ =>
     change (fun rho => ?A rho * ?B rho) with (A * B)
  end;

 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec (*;
 clear DependedTypeList*); 

 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
             destruct p as [a b]
       end;

 first [apply elim_close_precondition; [simpl; solve [auto 50 with closed] | solve [auto 50 with closed] | ]];
(* first [apply elim_close_precondition; [solve [auto 50 with closed] | solve [auto 50 with closed] | ]
        | erewrite compute_close_precondition by reflexivity].*)

 simplify_func_tycontext;
 repeat match goal with
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 try expand_main_pre_old;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP;
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH
                 | Share.t => intros ?SH
                 | _ => intro
                 end
               | |- _ => intro
               end);
(*
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
*)
 abbreviate_semax;
 lazymatch goal with 
 | |- semax ?Delta (PROPx _ (LOCALx ?L _)) _ _ => check_parameter_vals Delta L
 | _ => idtac
 end;
 try match goal with DS := @abbreviate (PTree.t funspec) PTree.Leaf |- _ =>
     clearbody DS
 end;
 start_function_hint.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
(* start_function.*) (* Always do this at the beginning of a semax_body proof *)
start_function1.
 { apply andp_left2. simpl; intros. apply sepcon_derives; [ | apply derives_refl ].
   apply (cp_o2i (rmaps.ConstType(val * share * list Z * Z))).
   apply compute_list_norepet_e; reflexivity. reflexivity. } 
 simpl in x. destruct x as [[[a sh] contents] size].
start_function2.

(* The next two lines do forward symbolic execution through
   the first two executable statements of the function body *)
forward.  (* i = 0; *)
forward.  (* s = 0; *)
(* To do symbolic execution through a [while] loop, we must
 * provide a loop invariant, so we use [forward_while] with
 * the invariant as an argument .*)
forward_while
 (EX i: Z,
   PROP  (0 <= i <= size)
   LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
(* forward_while leaves four subgoals; here we label them
   with the * bullet. *)
* (* Prove that current precondition implies loop invariant *)
Exists 0.   (* Instantiate the existential on the right-side of |--   *)
entailer!.  (* Simplify this entailment as much as possible; in this
      case, it solves entirely; in other cases, entailer! leaves subgoals *)
* (* Prove that loop invariant implies typechecking condition *)
entailer!.  (* Typechecking conditions usually solve quite easily *)
* (* Prove postcondition of loop body implies loop invariant *)
(* In order to get to the postcondition of the loop body, of course,
   we must forward-symbolic-execute through the loop body;
   so we start that here. *)
(* "forward" fails and tells us to first make (0 <= i < Zlength contents)
   provable by auto, so we assert the following: *)
assert_PROP (Zlength contents = size). {
  entailer!. do 2 rewrite Zlength_map. reflexivity.
}
forward. (* x = a[i] *)
forward. (* s += x; *)
forward. (* i++; *) 
 (* Now we have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the
   postcondition of the loop body) entails the loop invariant. *)
 Exists (i+1).
 entailer!. simpl.
 f_equal.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite sum_Z_app. rewrite (sublist_one i) by omega.
 autorewrite with sublist. normalize.
 simpl. rewrite Z.add_0_r. reflexivity. 
* (* After the loop *)(*
unfold POSTCONDITION, abbreviate. unfold frame_ret_assert, gfunction_body_ret_assert. simpl.
eapply semax_post.
5:{ forward. }
+ (*(function_body_ret_assert (ret_type Delta)
        (gassert2assert [] MPOST)) = ?*)
   unfold POSTCONDITION, abbreviate.
   unfold function_body_ret_assert, gfunction_body_ret_assert, frame_ret_assert.
   simpl; intros. entailer!.
+  unfold POSTCONDITION, abbreviate.
   unfold function_body_ret_assert, gfunction_body_ret_assert, frame_ret_assert.
   simpl; intros. entailer!.
+  unfold POSTCONDITION, abbreviate.
   unfold function_body_ret_assert, gfunction_body_ret_assert, frame_ret_assert.
   simpl; intros. entailer!.
+  unfold POSTCONDITION, abbreviate.
   unfold function_body_ret_assert, gfunction_body_ret_assert, frame_ret_assert.
   simpl; intros. entailer. apply andp_left2. rewrite gbind_ret_char; destruct vl; simpl.
   - unfold liftx, lift, gassert2assert; simpl. entailer. apply derives_refl'.
   unfold POSTCONDITION, abbreviate.
   unfold function_body_ret_assert, gfunction_body_ret_assert, frame_ret_assert.
   simpl; intros. entailer! unfold POSTCONDITION, abbreviate.
Search gfunction_body_ret_assert. hnf. rewrite gfunction_body_ret_assert_char.
 simpl. entailer.
entailer.
all: intros; entailer.
unfold POSTCONDITION, abbreviate.
Search Clight_seplog.AssertTT2ArgsTT.
unfold POSTCONDITION, abbreviate. Search gfunction_body_ret_assert. Clight_seplog.AssertTT2ArgsTT. Search  hnf.

forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
autorewrite with sublist in *.
autorewrite with sublist.
reflexivity.*)
Admitted.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
(* start_function.*)
start_function1.
 { apply andp_left2. simpl; intros. apply sepcon_derives; [ | apply derives_refl ].
   apply (cp_o2i (rmaps.ConstType(globals))).
   apply compute_list_norepet_e; reflexivity. reflexivity. } 
 simpl in gv.
start_function2.

Ltac prove_call_setup1 subsumes ::=
  match goal with
  | |- @semax _ _ _ (@exp _ _ _ _) _ _ =>
    fail 1 "forward_call fails because your precondition starts with EX.
Use Intros  to move          the existentially bound variables above the line"
  | |- @semax ?CS _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R'))) ?c _ => 
    match c with
    | context [Scall _ ?a ?bl] => 
      let R := strip1_later R' in idtac (*
      exploit (call_setup1_i CS Delta P Q (*R*) R' a bl);
      [check_prove_local2ptree
      |reflexivity
      |prove_func_ptr
      | apply subsumes
      |check_parameter_types
      |check_typecheck
      |check_typecheck
      |check_cast_params
     (* |reflexivity the pTrree_from_elements Qactuals check*)
      | ]*)
    | context [Scall _ (Evar ?id ?ty) ?bl] => fail 99 "L2" (*
      let R := strip1_later R' in
      exploit (call_setup1_i2 CS Delta P Q R' (*R*) id ty bl) ;
      [check_prove_local2ptree
      | apply can_assume_funcptr2; (*(can_assume_funcptr3 _ _ subsumes);*)
        [ check_function_name
        | lookup_spec id
        | find_spec_in_globals'
        | simpl; reflexivity  (* function-id type in AST matches type in funspec *)
        ]
      | apply subsumes
      | try reflexivity; (eapply classify_fun_ty_hack; [apply subsumes| reflexivity ..])  (* function-id type in AST matches type in funspec *)
      |check_typecheck
      |check_typecheck
      |check_cast_params
      (*|reflexivity the pTree_from_elements Qactuals check*)
      | ..
      ]*)
    end
  end.

Ltac prove_call_setup ts subsumes witness ::=
 prove_call_setup1 subsumes (*;
 [ .. | 
 match goal with |- call_setup1  _ _ _ _ _ _ _ _ (*_*) _ _ _ _ _ ?A _ _ _ _ _ _ _ -> _ =>
      check_witness_type ts A witness
 end;
 prove_call_setup_aux ts witness]*).

Ltac fwd_call' ts subsumes witness ::=
lazymatch goal with
| |- semax _ _ (Ssequence (Scall _ _ _) _) _ =>
  eapply semax_seq';
    [prove_call_setup ts subsumes witness(*!!;
     clear_Delta_specs; clear_MORE_POST;
     [ .. |
      lazymatch goal with
      | |- _ -> semax _ _ (Scall (Some _) _ _) _ =>(*
         forward_call_id1_wow'
      | |- call_setup2' _ _ _ _ _ _ _ _ _ _ _ _ ?retty _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> 
                semax _ _ (Scall None _ _) _ =>*)
         forward_call_id1_wow
      | |- call_setup2 _ _ _ _ _ _ _ _ _ _ _ _ ?retty _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> 
                semax _ _ (Scall None _ _) _ =>
        tryif (unify retty Tvoid)
        then forward_call_id00_wow(*'*)
        else forward_call_id01_wow(*'*)
     end]*)
   | after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Ecast (Etempvar ?ret'2 _) _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup ts subsumes witness(*!!;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_x_wow(*'*) ]*)
         |  after_forward_call ]
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?ret') _ _)
                                       (Sset _ (Etempvar ?ret'2 _))) _) _ =>
       unify ret' ret'2;
       eapply semax_seq';
         [prove_call_setup ts subsumes witness(*!!;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_y_wow(*'*) ]*)
         |  after_forward_call ]
| |- _ => rewrite <- seq_assoc; fwd_call' ts subsumes witness
end.

forward_call (*  s = sumarray(four,4); *)
  (gv _four, Ews,four_contents,4).

{ prove_call_setup ts subsumes witness;
          clear_Delta_specs; clear_MORE_POST;
             [ .. | forward_call_id1_y_wow(*'*) ].

 split3. auto. computable. repeat constructor; computable.
forward. (* return s; *)
Admitted.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.

Ltac prove_semax_prog_aux tac ::=
  match goal with
    | |- semax_prog ?prog ?z ?Vprog ?Gprog =>
     let x := constr:(ltac:(old_with_library prog Gprog))
     in change ( SeparationLogicAsLogicSoundness.MainTheorem.CSHL_MinimumLogic.CSHL_Defs.semax_prog
                    prog z Vprog x)
  end;
 split3; [ | | split3; [ | | split]];
 [ reflexivity || fail "duplicate identifier in prog_defs"
 | reflexivity || fail "unaligned initializer"
 | solve [solve_cenvcs_goal || fail "comp_specs not equal"]
   (*compute; repeat f_equal; apply proof_irr] || fail "comp_specs not equal"*)
 |
 | reflexivity || fail "match_globvars failed"
 | idtac (*match goal with
     |- match initial_world.find_id (prog_main ?prog) ?Gprog with _ => _ end =>
     unfold prog at 1; (rewrite extract_prog_main || rewrite extract_prog_main');
     ((eexists; reflexivity) || 
        idtac (*fail "Funspec of _main is not in the proper form"*) )
    end*)
 ]; try (
 match goal with |- semax_func ?V ?G ?g ?D ?G' =>
   let Gprog := fresh "Gprog" in 
   pose (Gprog := @abbreviate _ G); 
  change (semax_func V Gprog g D G')
 end;
 tac).

  prove_semax_prog.
  + semax_func_cons body_sumarray.
    semax_func_cons body_main.
  + simpl. eexists. apply semax_prog.Newfunspec_eq.
    - unfold main_pre, main_pre_old, Clight_seplog.AssertTT2ArgsTT. simpl.
      extensionality ts. extensionality glob. extensionality x. destruct x as [g vals].
      rewrite gglobvars2pred_unfold.
      unfold glift2, globvars2pred, lift2, glift0, lift0,
       Clight_seplog.mkEnv, globals_only, globals_of_env, globals_of_genv. simpl. 
      apply pred_ext; normalize.
      * destruct vals; unfold globals_only; simpl; entailer.
      * destruct vals; unfold globals_only; simpl; entailer.
    - reflexivity. 
Qed.
