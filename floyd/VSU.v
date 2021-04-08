Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.
Require Export VST.floyd.PTops.
Require Export VST.floyd.QPcomposite.
Require Export VST.floyd.quickprogram.
Require Export VST.floyd.Component.

Lemma valid_pointer_is_null_or_ptr p: valid_pointer p |-- !!( is_pointer_or_null p).
Proof. apply valid_pointer_is_pointer_or_null. Qed.

Lemma semax_body_subsumespec_VprogNil {cs V G f iphi}:
       @semax_body [] G cs f iphi ->
       list_norepet (map fst V ++ map fst G) ->
       @semax_body V G cs f iphi.
Proof. intros. eapply Component.semax_body_subsumespec. apply H.
+ intros i. red. 
  rewrite 2 semax_prog.make_context_g_char; trivial.
  destruct ((make_tycontext_s G) ! i); trivial. simpl; trivial.
  simpl. eapply list_norepet_append_right. apply H0.
+ intros. apply subsumespec_refl.
Qed.

Lemma semax_body_subsumespec_NilNil {cs V G f iphi}:
       @semax_body [] [] cs f iphi ->
       list_norepet (map fst V ++ map fst G) ->
       @semax_body V G cs f iphi.
Proof. intros. eapply semax_body_subsumespec_VprogNil; trivial. 
  eapply semax_body_subsumespec_GprogNil; trivial.
  simpl. eapply list_norepet_append_right. apply H0.
Qed.

Lemma init_data2pred_isptr {gv d sh v}:init_data2pred gv d sh v |-- !!(isptr v).
Proof. 
  destruct d; simpl; entailer. apply mapsto_zeros_isptr.
  destruct (gv i); entailer!.
Qed.

Lemma globvar2pred_headptr gv i u (G: globals_ok gv) (U: @gvar_init type u <> nil) (UU: @gvar_volatile type u = false):
      globvar2pred gv (i, u) |-- !! headptr (gv i).
Proof.
  destruct (G i). entailer!. rewrite H.
  unfold globvar2pred. simpl. rewrite UU, H.
  destruct (@gvar_init type u). elim U; trivial. simpl.
  sep_apply (@init_data2pred_isptr gv i0 (readonly2share (@gvar_readonly type u)) Vundef). entailer!.
Qed.

Lemma SF_ctx_subsumption {Espec} V G ge i fd phi cs
  (HSF:  @SF Espec cs V ge G i fd phi)
  (LNR_G: list_norepet (map fst G)) G' V' ge' cs'
  (SubCS: cspecs_sub cs cs')
  (FD: genv_find_func ge' i fd)
  (SubFG: forall j, sub_option (make_tycontext_g V G) ! j (make_tycontext_g V' G') ! j)
  (SubG: forall j : ident, subsumespec (find_id j G) (find_id j G')):
  @SF Espec cs' V' ge' G' i fd phi.
Proof.
  destruct fd; simpl.
 + eapply InternalInfo_subsumption.
    4: eapply (@InternalInfo_envs_sub cs cs' SubCS); eassumption.
    assumption. assumption. assumption. 
 + eapply ExternalInfo_envs_sub; eassumption.
Qed.

Lemma SF_ctx_extensional {Espec} V G ge i fd cs phi (HSF:  @SF Espec cs V ge G i fd phi)
  (LNR_G: list_norepet (map fst G)) G'
  (GG': forall j, find_id j G = find_id j G'):
  @SF Espec cs V ge G' i fd phi.
Proof.
  destruct fd; simpl; [ | apply HSF].
  eapply InternalInfo_subsumption; [ | | eassumption | eassumption].
  + intros j; red. remember ((make_tycontext_g V G) ! j) as q; destruct q; simpl; trivial.
    symmetry in Heqq. 
    specialize (semax_prog.make_tycontext_s_g V G j). 
    specialize (semax_prog.make_tycontext_s_g V G' j).
    rewrite 2 make_tycontext_s_find_id, GG'. intros.
    remember (find_id j G') as w; destruct w.
    * rewrite (H _ (eq_refl _)). rewrite (H0 _ (eq_refl _)) in Heqq; trivial.
    * clear H H0; symmetry in Heqw. specialize (GG' j); rewrite Heqw in GG'.
      rewrite semax_prog.make_tycontext_g_G_None by trivial. 
      rewrite semax_prog.make_tycontext_g_G_None in Heqq; trivial.
  + intros j; rewrite GG'. apply subsumespec_refl.
Qed.

Definition keep_fun {F} (externs: list ident) (ig: ident * globdef (fundef F) type) : bool :=
 match ig with
 | (_,Gvar _) => true 
 | (i, Gfun (Internal _)) => true
 | (i, Gfun (External _ _ _ _)) => in_dec ident_eq i externs
 end.

Definition prune_QPprogram {F} (p: QP.program F) (externs: list ident) : QP.program F :=
 {| QP.prog_builtins := p.(QP.prog_builtins);
     QP.prog_defs := PTree_filter (keep_fun externs) p.(QP.prog_defs);
     QP.prog_public := p.(QP.prog_public);
     QP.prog_main := p.(QP.prog_main);
     QP.prog_comp_env := p.(QP.prog_comp_env)
 |}.

(*******************Material related to automation *****************************)


Inductive SF_internal C V (ge : Genv.t Clight.fundef type) G id f phi:=
_SF_internal:
  (id_in_list id (map fst G) && semax_body_params_ok f)%bool = true ->
  Forall (fun it : ident * type => complete_type (@cenv_cs C)(snd it) = true) (fn_vars f) ->
  var_sizes_ok (*cenv_cs*) (fn_vars f) ->
  fn_callconv f = callingconvention_of_funspec phi ->
  semax_body V G f (id, phi) -> genv_find_func ge id (Internal f) ->
  SF_internal C V ge G id f phi.

Lemma SF_internal_sound {Espec cs V} {ge : Genv.t Clight.fundef type} G i f phi:
  SF_internal cs V ge G i f phi -> @SF Espec cs V ge G i (Internal f) phi.
Proof. simpl; intros. inv H. red. intuition. Qed.

Ltac findentry := repeat try first [ left; reflexivity | right].

Ltac finishComponent :=(*
    intros i phi E; simpl in E;
    repeat (if_tac in E;
            [inv E; eexists; split; [ reflexivity
                                    | try solve [apply funspec_sub_refl]]
            | ]);
    try solve [discriminate].*)
    intros i phi E; simpl in E;
    repeat (if_tac in E;
       [  inv E; first [ solve [apply funspec_sub_refl]
                    | eexists; split; [ reflexivity
                                    | try solve [apply funspec_sub_refl]]]
       | ]);
    try solve [discriminate].

Ltac lookup_tac := 
    intros H;
    repeat (destruct H; [ repeat ( first [ solve [left; trivial] | right]) | ]); try contradiction.

Lemma semax_vacuous:
 forall cs Espec Delta pp frame c post,
  @semax cs Espec Delta (fun rho => (close_precondition pp) FF rho * frame rho)%logic
      c post.
Proof.
intros.
eapply semax_pre; [ | apply semax_ff].
apply andp_left2.
intro rho.
rewrite sepcon_comm.
apply sepcon_FF_derives'.
unfold close_precondition.
apply exp_left; intro.
apply andp_left2.
unfold FF; simpl.
auto.
Qed.

Ltac SF_vacuous :=
   match goal with |- SF _ _ _ (vacuous_funspec _) => idtac end;
   repeat (split; [solve[constructor] | ]);
  split; [ | eexists; split; compute; reflexivity];
  split3; [reflexivity | reflexivity | intros ];
  apply semax_vacuous.

Lemma compspecs_ext:
 forall cs1 cs2 : compspecs,
 @cenv_cs cs1 = @cenv_cs cs2 ->
 @ha_env_cs cs1 = @ha_env_cs cs2 ->
 @la_env_cs cs1 = @la_env_cs cs2 ->
 cs1 = cs2.
Proof.
intros.
destruct cs1,cs2.
simpl in *; subst.
f_equal; apply proof_irr.
Qed.

Record compositeData :=
  { cco_su : struct_or_union;
    cco_members : members;
    cco_attr : attr;
    cco_sizeof : Z;
    cco_alignof : Z;
    cco_rank : nat }.

Definition getCompositeData (c:composite):compositeData. destruct c.
apply (Build_compositeData co_su co_members co_attr co_sizeof co_alignof co_rank).
Defined.

Lemma composite_env_ext:
 forall ce1 ce2, 
 PTree.map1 getCompositeData ce1 =
 PTree.map1 getCompositeData ce2 ->
 ce1 = ce2.
Proof.
induction ce1; destruct ce2; simpl; intros; auto; try discriminate.
inv H.
f_equal; auto.
destruct o,o0; inv H2; auto.
clear - H0.
f_equal.
destruct c,c0; inv H0; simpl in *; subst; f_equal; apply proof_irr.
Qed.

Definition QPprog {cs: compspecs} (p: Clight.program) :=
  QPprogram_of_program p ha_env_cs la_env_cs.

Definition compspecs_of_QPprogram (prog: Clight.program)
          ha_env la_env OK :=
compspecs_of_QPcomposite_env
  (QP.prog_comp_env
     (QPprogram_of_program prog ha_env la_env)) OK.

Lemma compspecs_eq_of_QPcomposite_env:
forall cs (prog: Clight.program) OK,
 PTree.map1 getCompositeData (@cenv_cs cs) =
 PTree.map1 getCompositeData (prog_comp_env prog) ->
 PTree_samedom  (@cenv_cs cs) (@ha_env_cs cs) ->
 PTree_samedom  (@cenv_cs cs) (@la_env_cs cs) ->
 cs = compspecs_of_QPprogram prog (@ha_env_cs cs) (@la_env_cs cs) OK.
Proof.
intros.
assert (@cenv_cs cs = prog_comp_env prog)
 by (apply composite_env_ext; auto).
destruct OK as [? [? [? [? [? [? ?]]]]]].
simpl.
apply compspecs_ext; simpl.
clear - H0 H1 H2.
unfold QPprogram_of_program in x.
simpl in x.
forget (prog_comp_env prog) as ce.
clear prog.
subst ce.
rewrite composite_env_of_QPcomposite_env_of_composite_env. auto.
apply PTree_samedom_domain_eq; auto.
apply PTree_samedom_domain_eq; auto.
unfold QPcomposite_env_of_composite_env.
rewrite PTree_map1_map3.
symmetry; apply PTree_map3_2; rewrite <- H2; auto.
unfold QPcomposite_env_of_composite_env.
rewrite PTree_map1_map3.
symmetry; apply PTree_map3_3; rewrite <- H2; auto.
Qed.

Lemma QPcompspecs_OK_i':
 forall (cs: compspecs) ce ha la, 
 ce = @cenv_cs cs ->
 ha = @ha_env_cs cs ->
 la = @la_env_cs cs ->
 @PTree_samedom composite Z ce ha->
 @PTree_samedom composite legal_alignas_obs ce la ->
 QPcompspecs_OK
    (QPcomposite_env_of_composite_env ce ha la).
Proof.
intros.
subst.
apply QPcompspecs_OK_i; auto.
Qed.

Ltac decompose_in_elements H :=
match type of H with
 | (?i,_)=_ \/ _ => 
   destruct H as [H|H];
   [let j := eval compute in i in change i with j in H;
                injection H; clear H; intros; subst 
  | decompose_in_elements H ]
 | False => contradiction H
 | _ => idtac
 end.

Fixpoint fold_ident {A} (i: positive) (al: list (ident * A)) : ident :=
 match al with
 | (j,_)::al' => if Pos.eqb i j then j else fold_ident i al'
 | nil => i
end.

Definition isSomeGfunExternal {F V} (d: option(globdef (fundef F) V)) : bool :=
 match d with Some(Gfun(External _ _ _ _)) => true | _ => false end.
Definition Comp_Externs_OK (E: funspecs) (p: QP.program Clight.function) :=
  Forall (fun i => isSomeGfunExternal ((QP.prog_defs p) ! i) = true) (map fst E).

Lemma compute_Comp_Externs: forall (E: funspecs) (p: QP.program Clight.function),
Comp_Externs_OK (E: funspecs) (p: QP.program Clight.function) ->
(forall i : ident,
In i (map fst E) ->
exists f ts t cc, (QP.prog_defs p) ! i = Some (Gfun (External f ts t cc))).
Proof.
intros.
red in H.
rewrite Forall_forall in H.
apply  H in H0; clear H.
unfold isSomeGfunExternal in H0.
destruct ((QP.prog_defs p) ! i); try discriminate.
destruct g; try discriminate.
destruct f; try discriminate.
eauto.
Qed.

Definition compute_missing_Comp_Externs (E: funspecs) (p: QP.program Clight.function) : list ident :=
 filter (fun i => negb(isSomeGfunExternal ((QP.prog_defs p)!i))) (map fst E).

Ltac check_Comp_Externs :=
 apply compute_Comp_Externs;
 (solve [repeat apply Forall_cons; try apply Forall_nil; reflexivity]
  || match goal with |- Comp_Externs_OK ?E ?p =>
      let ids := constr:(compute_missing_Comp_Externs E p) in
      let ids := eval hnf in ids in let ids := eval simpl in ids in
      fail "The following identifiers are proposed as 'Extern' funspecs, but the Clight program does not list them as Gfun(External _ _ _ _):"
               ids
      end).

Ltac check_Comp_Imports_Exports :=
 apply compute_Comp_Externs;
 (solve [repeat apply Forall_cons; try apply Forall_nil; reflexivity]
  || match goal with |- Comp_Externs_OK ?E ?p =>
      let ids := constr:(compute_missing_Comp_Externs E p) in
      let ids := eval hnf in ids in let ids := eval simpl in ids in
      fail "The following identifiers are proposed as 'Imports' funspecs, but the Clight program does not list them as Gfun(External _ _ _ _):"
               ids
      end).

Lemma forallb_isSomeGfunExternal_e:
  forall {F} (defs: PTree.t (globdef (fundef F) type)) (ids: list ident),
   forallb (fun i => isSomeGfunExternal (defs ! i)) ids = true ->
  forall i : ident,
  In i ids ->
  exists f ts t cc, defs ! i = Some (Gfun (External f ts t cc)).
Proof.
intros.
rewrite forallb_forall in H.
apply H in H0. destruct (defs ! i) as [[[]|]|]; inv H0.
eauto.
Qed. 

Fixpoint faster_find_id {A} i (al: list (ident * A)) :=
match al with
| nil => None
| (j,x)::r => if eqb_ident i j then Some x else faster_find_id i r
end.

Lemma find_id_faster: @find_id = @faster_find_id.
Proof.
extensionality A i al.
induction al as [|[j?]]; simpl; auto.
if_tac. subst.
rewrite eqb_ident_refl; auto.
rewrite eqb_ident_false; auto.
Qed.

Lemma filter_options_in:
 forall {A B} (f: A -> option B) a b al,
   f a = Some b ->
   In a al ->
   In b (filter_options f al).
Proof.
induction al; simpl; intros; auto.
destruct H0.
subst.
rewrite H.
left; auto.
destruct (f a0); auto.
right; auto.
Qed.

Lemma prove_G_justified:
 forall Espec cs V p Imports G,
 let SFF := @SF Espec cs V (QPglobalenv p) (Imports ++ G) in
 let obligations := filter_options (fun (ix: ident * funspec) => let (i,phi) := ix in 
               match (QP.prog_defs p) ! i with
               | Some (Gfun fd) => Some (SFF i fd phi)
               | _ => None
               end) G in
 Forall (fun x => x) obligations ->
 (forall i phi fd, (QP.prog_defs p) ! i = Some (Gfun fd) ->
  find_id i G = Some phi ->
  @SF Espec cs V (QPglobalenv p) (Imports ++ G) i fd phi).
Proof.
intros.
subst SFF.
rewrite Forall_forall in H.
apply H; clear H.
subst obligations.
apply find_id_e in H1.
eapply filter_options_in; try eassumption.
simpl.
rewrite H0.
auto.
Qed.

Ltac compute_list p :=
 let a := eval hnf in p in 
 match a with
 | nil => uconstr:(a)
 | ?h :: ?t  => 
    let h := eval hnf in h in 
    match h with (?i,?x) => let i := eval compute in i in
       let t := compute_list t in
       uconstr:((i,x)::t)
     end
 end.

Ltac compute_list' p :=
  (* like compute_list but uses simpl instead of compute on the identifiers *)
 let a := eval hnf in p in 
 match a with
 | nil => uconstr:(a)
 | ?h :: ?t  => 
    let h := eval hnf in h in 
    match h with (?i,?x) => let i := eval simpl in i in
       let t := compute_list' t in
       uconstr:((i,x)::t)
     end
 end.

Ltac test_Component_prog_computed' :=
lazymatch goal with
 | |- Component _ _ _ (QPprog _) _ _ _ => 
       fail 1  "The QPprog of this component is of the form (QPprog _), which has not been calculated out to normal form.  Perhaps you meant   ltac:(QPprog _) instead of (QPprog _) in the theorem statement"
 | |- Component _ _ _ (@abbreviate _ {| QP.prog_builtins := _;
         QP.prog_defs := _; QP.prog_public := _;
       QP.prog_main := _;    QP.prog_comp_env := _ |}) _ _ _ =>
    fail 0 "success"
 | |- Component _ _ _ abbreviate _ _ _ => 
     fail 1 "The QPprog of this component is not in normal form"
 | |- Component _ _ _ ?p _ _ _ => 
        tryif unfold p then test_Component_prog_computed'
            else fail 1  "The QPprog of this component is not in normal form"
 | |- _ => fail 1 "The proof goal is not a Component"
 end.

Ltac test_Component_prog_computed :=
 try test_Component_prog_computed'.

Ltac mkComponent prog :=
 hnf;
 match goal with |- Component _ _ ?IMPORTS _ _ _ _ =>
     let i := compute_list' IMPORTS in change_no_check IMPORTS with i 
 end;
 test_Component_prog_computed;
 let p := fresh "p" in
 match goal with |- @Component _ _ _ _ ?pp _ _ _ => set (p:=pp) end;
 let HA := fresh "HA" in 
   assert (HA: PTree_samedom cenv_cs ha_env_cs) by repeat constructor;
 let LA := fresh "LA" in 
   assert (LA: PTree_samedom cenv_cs la_env_cs) by repeat constructor;
 let OK := fresh "OK" in
 assert (OK: QPprogram_OK p);
 [split; [apply compute_list_norepet_e; reflexivity | ];
   simpl;
   simple apply (QPcompspecs_OK_i' _);
   [ apply composite_env_ext; repeat constructor | reflexivity | reflexivity | assumption | assumption ]
 | ];
 (* Doing the  set(myenv...), instead of before proving the CSeq assertion,
     prevents nontermination in some cases  *)
 pose (myenv:= (QP.prog_comp_env (QPprogram_of_program prog ha_env_cs la_env_cs)));
 assert (CSeq: _ = compspecs_of_QPcomposite_env myenv 
                     (proj2 OK))
   by (apply compspecs_eq_of_QPcomposite_env;
          [reflexivity | assumption | assumption]);
 subst myenv;
 change (QPprogram_of_program prog ha_env_cs la_env_cs) with p in CSeq;
 clear HA LA;
 exists OK;
  [ check_Comp_Imports_Exports
  | apply compute_list_norepet_e; reflexivity || fail "Duplicate funspec among the Externs++Imports"
  | apply compute_list_norepet_e; reflexivity || fail "Duplicate funspec among the Exports"
  | apply compute_list_norepet_e; reflexivity
  | apply forallb_isSomeGfunExternal_e; reflexivity
  | intros; simpl; split; trivial; try solve [lookup_tac]
  | let i := fresh in let H := fresh in 
    intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; reflexivity |]); try contradiction
  | apply prove_G_justified;
    repeat apply Forall_cons; [ .. | apply Forall_nil];
    try SF_vacuous
  | finishComponent
  | first [ solve [intros; apply derives_refl] | solve [intros; reflexivity] | solve [intros; simpl; cancel] | idtac]
  ].

Ltac mkVSU prog internal_specs := 
 lazymatch goal with |- VSU _ _ _ _ _ => idtac
  | _ => fail "mkVSU must be applied to a VSU goal"
 end;
 exists internal_specs;
 mkComponent prog.

Ltac solve_SF_internal P :=
  apply SF_internal_sound; eapply _SF_internal;
   [  reflexivity 
   | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
   | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
   | reflexivity
   | match goal with OK: QPprogram_OK _, CSeq: @eq compspecs _ _ |- _ =>
       rewrite <- CSeq;
       clear CSeq OK
     end;
     (apply P ||
      idtac "solve_SF_internal did not entirely succeed, because" P "does not exactly match this subgoal")
   | eexists; split; 
       [ fast_Qed_reflexivity || fail "Lookup for a function identifier in QPglobalenv failed"
       | fast_Qed_reflexivity || fail "Lookup for a function pointer block in QPglobalenv failed"
   ]    ].

(*slightly slower*)
Ltac solve_SF_external_with_intuition B :=
   first [simpl; split; intuition; [ try solve [entailer!] | try apply B | eexists; split; cbv; reflexivity ] | idtac].

(*Slightly faster*)
Ltac solve_SF_external B :=
  first [ split3;
            [ reflexivity 
            | reflexivity 
            | split3;
                [ reflexivity
                | reflexivity
                | split3;
                   [ left; trivial
                   | clear; intros ? ? ? ?; try solve [entailer!];
                     repeat match goal with |- (let (y, z) := ?x in _) _ && _ |--  _ =>
                                     destruct x as [y z]
                     end
                    | split; [ try apply B | eexists; split; cbv; reflexivity ]
            ] ] ]
        | idtac ].

Fixpoint FDM_entries (funs1 funs2 : list (ident * fundef function)): option (list (ident * fundef function * fundef function)) :=
  match funs1 with
    nil => Some nil
  | (i, fd1) :: funs => match find_id i funs2 with 
                           None => FDM_entries funs funs2 
                         | Some fd2 => match FDM_entries funs funs2 with
                                         None => None
                                       | Some l => Some ((i, fd1, fd2) :: l)
                                       end
                        end
  end.

Definition check_FDM_entry (Imports1 Imports2:funspecs)  x :=
  match x with (i, fd1, fd2) =>
   match fd1, fd2 with
      Internal _, Internal _ => fd1 = fd2
    | Internal _, External _ _ _ _ => match find_id i Imports2 with
                                        None => False
                                      | Some phi2 => signature_of_fundef fd1 = signature_of_fundef fd2
                                      end
    | External _ _ _ _, Internal _ => match find_id i Imports1 with
                                        None => False
                                      | Some phi1 => signature_of_fundef fd1 = signature_of_fundef fd2
                                      end
    | External _ _ _ _, External _ _ _ _ => fd1 = fd2
   end
  end.

Lemma FDM {p1 p2 Imports1 Imports2}: forall entries,
  FDM_entries (QPprog_funct p1) (QPprog_funct p2) = Some entries ->
  Forall (check_FDM_entry Imports1 Imports2) entries ->
  Fundefs_match p1 p2 Imports1 Imports2.
Proof. 
  intros.
  hnf; intros.
  unfold QPprog_funct in H.
  rewrite <- find_id_elements in H1, H2.
  forget (PTree.elements (QP.prog_defs p1)) as d1.
  forget (PTree.elements (QP.prog_defs p2)) as d2.
  clear p1 p2.
  revert d2 H2 entries H H0; induction d1 as [|[j [?|?]]]; simpl; intros.
  -
   inv H. inv H1.
  -
    simpl in H1.
    if_tac in H1.
    +
      subst j. inv H1.
      assert (find_id i (QPprog_funct' d2) = Some fd2). {
         clear - H2.
         induction d2 as [|[??]]; simpl in *. inv H2.
         if_tac in H2. inv H2. simpl. rewrite if_true by auto. auto.
         apply IHd2 in H2. destruct g. simpl. rewrite if_false by auto; auto. auto.
      }
      rewrite H1 in H.
      destruct (FDM_entries (QPprog_funct' d1) (QPprog_funct' d2)) eqn:?H; inv H.
      inv H0. hnf in H5.
      destruct fd1, fd2; auto.
      destruct (find_id i Imports2) eqn:?H; try contradiction; eauto.
      destruct (find_id i Imports1) eqn:?H; try contradiction; eauto.
   +
       specialize (IHd1 H1).
       destruct (find_id j (QPprog_funct' d2)) eqn:?H.
     *
       destruct (FDM_entries (QPprog_funct' d1) (QPprog_funct' d2)) eqn:?H; inv H.
       inv H0. eapply IHd1; eauto.
     * eapply IHd1;  eauto.
  -
    simpl in H1.
    if_tac in H1. inv H1.
    eapply IHd1; eauto.
Qed.

Ltac prove_cspecs_sub := 
   try solve [split3; intros ?i; apply sub_option_get; repeat constructor].

Ltac solve_entry H H0:=
     inv H; inv H0; first [ solve [ trivial ] | split; [ reflexivity | eexists; reflexivity] ].

Definition list_disjoint_id (al bl: list ident) :=
  Forall (fun i => id_in_list i bl = false) al.

Lemma list_disjoint_id_e: 
 forall (al bl: list ident), 
  (list_disjoint_id al bl) ->
  list_disjoint al bl.
Proof.
intros.
induction H.
intros ? ? ? ? ?. inv H.
apply id_in_list_false in H.
apply list_disjoint_cons_l; auto.
Qed.

Ltac LDI_tac := 
   apply Forall_nil ||  (apply Forall_cons; [ reflexivity | LDI_tac ]).

Ltac LNR_tac := apply compute_list_norepet_e; reflexivity.

Definition compute_list_disjoint_id (al bl: list ident) :=
 let m := PTree_Properties.of_list (map (fun i => (i,tt)) al)
 in forallb (fun i => isNone (PTree.get i m)) bl.

Lemma compute_list_disjoint_id_e:
 forall al bl, compute_list_disjoint_id al bl = true ->
  list_disjoint al bl.
Proof.
intros.
unfold compute_list_disjoint_id in H.
rewrite forallb_forall in H.
intros i j ? ? ?; subst j.
apply H in H1.
apply (in_map (fun i : ident => (i, tt))) in H0.
apply (in_map fst) in H0.
apply PTree_Properties.of_list_dom in H0.
destruct H0.
simpl in H0.
rewrite H0 in H1. inv H1.
Qed.

Ltac list_disjoint_tac := 
  apply compute_list_disjoint_id_e; reflexivity.

Ltac ExternsHyp_tac := first [ reflexivity | idtac ].

Inductive Identifier_not_found: ident -> funspecs -> Prop := .
Inductive Funspecs_must_match (i: ident) (f1 f2: funspec):  Prop := 
mk_Funspecs_must_match: f1=f2 -> Funspecs_must_match i f1 f2.

Fixpoint SC_test (ids: list ident) (fds1 fds2: funspecs) : Prop :=
 match fds1 with
 | (i,fd)::fds' => if id_in_list i ids
                         then match initial_world.find_id i fds2 with
                                 | Some fd2 => Funspecs_must_match i fd fd2 
                                 | None => Identifier_not_found i fds2
                                 end /\ SC_test ids fds' fds2
                         else SC_test ids fds' fds2
 | nil => True
 end.

Lemma SC_lemma: forall (ids: list ident) (fds1 fds2: funspecs),
 SC_test ids fds1 fds2 ->
(forall (i:ident) (phi1: funspec),
  initial_world.find_id i fds1 = Some phi1 ->
  In i ids ->
  exists phi2 : funspec, 
  initial_world.find_id i fds2 = Some phi2 /\ funspec_sub phi2 phi1).
Proof.
intros ? ? ?.
induction fds1 as [|[i?]]; simpl; intros.
inv H0.
if_tac in H0.
subst i0; inv H0.
rewrite assoclists.id_in_list_true_i in H by auto.
destruct H.
destruct (initial_world.find_id i fds2) eqn:?H.
inv H.
exists f; split; auto.
apply funspec_sub_refl.
inv H.
destruct (id_in_list i ids) eqn:?H.
destruct H.
destruct (initial_world.find_id i fds2) eqn:?H.
eauto.
eauto.
eauto.
Qed.

Lemma VSULink': 
    forall Espec E1 Imports1 p1 Exports1 E2 Imports2 p2 Exports2
         GP1 GP2
         (vsu1 : @VSU Espec E1 Imports1 p1 Exports1 GP1)
         (vsu2 : @VSU Espec E2 Imports2 p2 Exports2 GP2)
         E Imports p Exports,
       E = G_merge E1 E2 ->
       Imports = VSULink_Imports vsu1 vsu2 ->
       Exports = G_merge Exports1 Exports2 ->
       QPlink_progs p1 p2 = Errors.OK p ->
       Fundefs_match p1 p2 Imports1 Imports2 ->
       list_disjoint_id (map fst E1) (IntIDs p2) ->
       list_disjoint_id (map fst E2) (IntIDs p1) ->
       SC_test (map fst E1 ++ IntIDs p1) Imports2 Exports1 ->
       SC_test (map fst E2 ++ IntIDs p2) Imports1 Exports2 ->
       (forall (i : ident) (phi1 phi2 : funspec),
        initial_world.find_id i Imports1 = Some phi1 ->
        initial_world.find_id i Imports2 = Some phi2 ->
        phi1 = phi2) ->
       VSU E Imports p Exports (GP1 * GP2)%logic.
Proof.
intros.
subst.
eapply VSULink; try eassumption.
apply list_disjoint_id_e; auto.
apply list_disjoint_id_e; auto.
apply SC_lemma; auto.
apply SC_lemma; auto.
Qed.

Definition compute_FDM_entry (Imports1 Imports2 : funspecs)
     (x : ident * fundef function * fundef function) : bool :=
 match x with ((i,fd1),fd2) =>
  match fd1 with
  | Internal _ =>
    match fd2 with
    | Internal _ => fundef_eq fd1 fd2
    | External _ _ _ _ =>
        match initial_world.find_id i Imports2 with
        | Some _ =>
            eqb_signature (signature_of_fundef fd1) (signature_of_fundef fd2)
        | None => false
        end
    end
| External _ _ _ _ =>
    match fd2 with
    | Internal _ =>
        match initial_world.find_id i Imports1 with
        | Some _ =>
            eqb_signature (signature_of_fundef fd1) (signature_of_fundef fd2)
        | None => false
        end
    | External _ _ _ _ => fundef_eq fd1 fd2
    end
end end.

Lemma compute_FDM_entry_e:
  forall Imports1 Imports2 x, 
   compute_FDM_entry Imports1 Imports2 x = true ->
   check_FDM_entry Imports1 Imports2 x.
Proof.
unfold compute_FDM_entry, check_FDM_entry.
intros.
destruct x as [[? ?] ?].
destruct f,f0; try discriminate.
apply fundef_eq_prop; auto.
destruct (initial_world.find_id i Imports2); try discriminate.
apply eqb_signature_prop; auto.
destruct (initial_world.find_id i Imports1); try discriminate.
apply eqb_signature_prop; auto.
apply fundef_eq_prop; auto.
Qed.

Definition compute_FDM p1 p2 Imports1 Imports2 : bool :=
 match FDM_entries (QPprog_funct p1) (QPprog_funct p2) with
 | None => false
 | Some entries => 
    forallb (compute_FDM_entry Imports1 Imports2) entries
 end.

Lemma compute_FDM_e:
  forall p1 p2 Imports1 Imports2,
    compute_FDM p1 p2 Imports1 Imports2 = true ->
    Fundefs_match p1 p2 Imports1 Imports2.
Proof.
  intros.
  unfold compute_FDM in H.
  destruct (FDM_entries (QPprog_funct p1) (QPprog_funct p2)) eqn:?H; inv H.
  eapply FDM. eassumption.
  apply Forall_forall.
  rewrite forallb_forall in H2.
  intros. apply compute_FDM_entry_e; auto.
Qed.

Definition compute_intersection  (Imports1 Imports2: funspecs) :
    list (ident * (funspec * funspec)) :=
 filter_options (fun ix => match initial_world.find_id (fst ix) Imports2 with
                              | Some phi => Some (fst ix, (snd ix, phi))
                              | None => None end) Imports1.

Definition imports_agree1 (ixy : ident * (funspec * funspec)) : Prop :=
 fst(snd ixy) = snd (snd ixy).

Definition imports_agree (Imports1 Imports2: funspecs) : Prop :=
  Forall imports_agree1 (compute_intersection Imports1 Imports2).

Definition imports_agree_e: forall Imports1 Imports2,
 imports_agree Imports1 Imports2 ->
       (forall (i : ident) (phi1 phi2 : funspec),
        initial_world.find_id i Imports1 = Some phi1 ->
        initial_world.find_id i Imports2 = Some phi2 ->
        phi1 = phi2).
Proof.
 intros.
 red in H.
 rewrite Forall_forall in H.
 apply (H (i,(phi1,phi2))); clear H.
 unfold compute_intersection.
 apply initial_world.find_id_e in H0.
 induction Imports1 as [|[j?]]. inv H0.
 simpl in H0. destruct H0.
 inv H. simpl.
 rewrite H1. left; auto.
 simpl.
 specialize (IHImports1 H).
 destruct (initial_world.find_id j Imports2) eqn:?H.
 simpl.
 right; auto.
 auto.
Qed.

Lemma VSULink'': 
    forall Espec E1 Imports1 p1 Exports1 E2 Imports2 p2 Exports2
         GP1 GP2
         (vsu1 : @VSU Espec E1 Imports1 p1 Exports1 GP1)
         (vsu2 : @VSU Espec E2 Imports2 p2 Exports2 GP2)
         E Imports p Exports,
       E = G_merge E1 E2 ->
       Imports = VSULink_Imports vsu1 vsu2 ->
       Exports = G_merge Exports1 Exports2 ->
       QPlink_progs p1 p2 = Errors.OK p ->
       compute_FDM p1 p2 Imports1 Imports2 = true ->
       compute_list_disjoint_id (map fst E1) (IntIDs p2) = true ->
       compute_list_disjoint_id (map fst E2) (IntIDs p1) = true ->
       SC_test (map fst E1 ++ IntIDs p1) Imports2 Exports1 ->
       SC_test (map fst E2 ++ IntIDs p2) Imports1 Exports2 ->
       imports_agree Imports1 Imports2 ->
       VSU E Imports p Exports (GP1 * GP2)%logic.
Proof.
intros.
subst.
eapply VSULink; try eassumption.
apply compute_FDM_e; auto.
apply compute_list_disjoint_id_e; auto.
apply compute_list_disjoint_id_e; auto.
apply SC_lemma; auto.
apply SC_lemma; auto.
apply imports_agree_e; auto.
Qed.

Ltac HImports_tac' := clear; repeat apply Forall_cons; try apply Forall_nil; 
     (reflexivity || match goal with |- imports_agree ?i _ _ =>
                       fail "Imports disagree at identifier" i end).

Ltac SC_tac :=
 match goal with |- SC_test ?ids _ _ =>
  let a := eval compute in ids in change ids with a
 end;
 hnf;
 repeat (apply conj; hnf);
 lazymatch goal with
         | |- Funspecs_must_match ?i _ _ =>
                 try solve [constructor; unfold abbreviate; repeat f_equal]
         | |- Identifier_not_found ?i ?fds2 =>
                 fail "identifer" i "not found in funspecs" fds2
         | |- True => trivial
          end.

Ltac HImports_tac := simpl;
  let i := fresh "i" in 
   intros i ? ? H1 H2;
  repeat (if_tac in H1; subst; simpl in *; try discriminate);
    (first [ congruence | inv H1; inv H2; reflexivity | fail "Imports disagree at identifier" i] ).

Ltac ImportsDef_tac := first [ reflexivity | idtac ].
Ltac ExportsDef_tac := first [ reflexivity | idtac ].
Ltac domV_tac := compute; tauto.

Ltac find_id_subset_tac := simpl; intros ? ? H;
  repeat (if_tac in H; [ inv H; simpl; try reflexivity | ]); discriminate.

Ltac ComponentMerge C1 C2 :=
  eapply (ComponentJoin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 C2);
[ list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| list_disjoint_tac
| LNR_tac
| LNR_tac
| prove_cspecs_sub
| prove_cspecs_sub
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
(*| FDM_tac *)
(*| FunctionsPreserved_tac *)
| apply list_disjoint_id_e; LDI_tac
| apply list_disjoint_id_e; LDI_tac
| ExternsHyp_tac
| apply SC_lemma; SC_tac
| apply SC_lemma; SC_tac
| HImports_tac
(*+  HContexts. This is the side condition we'd like to exliminate - it's also
   why we need to define SubjectComponent/ObserverComponent using DEFINED
  simpl; intros.
  repeat (if_tac in H; [ inv H; inv H0 | ]). discriminate.*)
| ImportsDef_tac
| ExportsDef_tac
| LNR_tac
| LNR_tac
| domV_tac
| try (cbv; reflexivity)
| try (cbv; reflexivity)
| try (cbv; reflexivity) 
| first [ find_id_subset_tac | idtac]
| first [ find_id_subset_tac | idtac]
].

Lemma VSU_ext {Espec E Imp p Exp GP1 GP2}:
      @VSU Espec E Imp p Exp GP1 -> GP1=GP2 ->
      @VSU Espec E Imp p Exp GP2.
Proof. intros; subst; trivial. Qed.

Ltac compute_QPlink_progs := 
match goal with |- ?A = _ => 
  let p1 := eval hnf in A in
  lazymatch p1 with
 | Errors.Error ?m => fail m
 | Errors.OK ?p' => instantiate (1:=@abbreviate _ p'); reflexivity
 | _ => fail "could not reduce QPlink_prog to hnf"
 end
end.

Ltac FDM_tac := 
  try (apply compute_FDM_e;  reflexivity);
  fail "FDM_tac failed".

Ltac VSULink_tac := 
eapply VSULink;
[ compute_QPlink_progs
| FDM_tac
| list_disjoint_tac
| list_disjoint_tac
| apply SC_lemma; SC_tac
| apply SC_lemma; SC_tac
| HImports_tac].

Ltac red_until_NDmk_funspec x :=
 lazymatch x with
 | NDmk_funspec _ _ _ _ _ => uconstr:(x)
 | mk_funspec _ _ _ _ _ _ _ => uconstr:(x)
 | merge_specs ?A ?B => 
     let b := eval hnf in B in 
     match b with None => uconstr:(A) | _ => uconstr:(merge_specs A b) end
 | _ => uconstr:(x)
 end.

Ltac simplify_funspecs G :=
  let x := eval hnf in G in 
 lazymatch x with
 | nil => constr:(x)
 | ?ia :: ?al => let al := simplify_funspecs al in
                       let ia := eval hnf in ia in
                       match ia with pair  ?i ?a =>
                             let b := red_until_NDmk_funspec a in
                              constr:( (i,@abbreviate _ b)::al )
                       end
 end.

Ltac compute_VSULink_Imports v1 v2 := 
  let Imports := uconstr:(VSULink_Imports v1 v2) in
  let x := eval cbv beta delta [VSULink_Imports] in Imports in
  match x with VSULink_Imports_aux ?I1 ?I2 ?A ?B =>
    let k1 := eval compute in A in
    let k2 := eval compute in B in
    let x := uconstr:(VSULink_Imports_aux I1 I2 k1 k2) in
    simplify_funspecs x
 end.

Definition privatize_ids (ids: list ident) (fs: funspecs) : funspecs :=
 filter (fun ix => negb (id_in_list (fst ix) ids)) fs.

Lemma privatize_sub_option:
 forall ids fs, 
 list_norepet (map fst fs) ->
 forall i, PTops.sub_option
       (initial_world.find_id i (privatize_ids ids fs))
       (initial_world.find_id i fs).
Proof.
intros.
hnf.
destruct (initial_world.find_id i (privatize_ids ids fs)) eqn:?H; auto.
apply assoclists.find_id_filter_Some in H0; auto.
destruct H0; auto.
Qed.

Lemma privatizeExports
   {Espec E Imports p Exports GP} (v: @VSU Espec E Imports p Exports GP)
   (ids: list ident)  :
  @VSU Espec E Imports p (privatize_ids ids Exports) GP.
Proof.
destruct v as [G comp].
exists G.
apply (Comp_Exports_sub2 _ _ _ _ _ _ _ _ comp).
apply assoclists.list_norepet_map_fst_filter.
apply (Comp_Exports_LNR comp).
apply privatize_sub_option.
apply (Comp_Exports_LNR comp).
Qed.

Definition restrictExports {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (Exports': funspecs) :=
   @VSU Espec E Imports p Exports' GP.

Definition funspec_sub_in (fs: funspecs) (ix: ident * funspec) :=
  match find_id (fst ix) fs with
  | Some f => funspec_sub f (snd ix)
  | None => False
 end.

Lemma prove_restrictExports
   {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (Exports': funspecs) :
   list_norepet (map fst Exports') ->
   Forall (funspec_sub_in Exports) Exports' ->
   restrictExports v Exports'.
Proof.
intros.
destruct v as [G c].
exists G.
apply (@Build_Component _ _ _ _ _ _ _ _ (Comp_prog_OK c)); try apply c; auto.
+ intros.
  rewrite Forall_forall in H0.
  apply find_id_e in E0.
  apply H0 in E0.
  red in E0.
  simpl in E0.
  destruct (find_id i Exports) eqn:?H; try contradiction.
  apply (Comp_G_Exports c) in H1.
  destruct (find_id i G). eapply funspec_sub_trans; eauto. 
  destruct H1 as [phi' [? ?]].
  exists phi'.
  split; auto.
  eapply funspec_sub_trans; eauto.
+ intros. apply (Comp_MkInitPred c); auto.
Qed.

Ltac prove_restrictExports :=
 simple apply prove_restrictExports; 
   [apply compute_list_norepet_e; reflexivity || fail "Your restricted Export list has a duplicate function name"
   | repeat apply Forall_cons; try simple apply Forall_nil;
       red; simpl find_id; cbv beta iota;
       change (@abbreviate funspec ?A) with A
   ].


(*A Variant of prove_restrictExports that uses "Forall2 funspec_sub"
  rather than Forall  "Forall (funspec_sub_in ..)"*)
Lemma prove_restrictExports2
   {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (Exports': funspecs) :
   map fst Exports' = map fst Exports ->
   Forall2 funspec_sub (map snd Exports) (map snd Exports') ->
   restrictExports v Exports'.
Proof.
intros.
destruct v as [G c].
exists G.
apply (@Build_Component _ _ _ _ _ _ _ _ (Comp_prog_OK c)); try apply c; auto.
+ rewrite H. apply c.
+ intros. destruct (find_funspec_sub Exports' Exports H H0 _ _ E0) as [psi [Psi PSI]].
  apply (Comp_G_Exports c) in Psi.
  destruct (find_id i G). eapply funspec_sub_trans;eauto.
  destruct Psi as [tau [Tau TAU]].
  exists tau; split; trivial. eapply funspec_sub_trans; eassumption.
+ apply (Comp_MkInitPred c).
Qed.

Ltac prove_restrictExports2 :=
 simple apply prove_restrictExports; 
   [apply compute_list_norepet_e; reflexivity || fail "Your restricted Export list has a duplicate function name"
   | 
   ].


Fixpoint replace_spec (specs:funspecs) p (phi:funspec):funspecs :=
  match specs with
     [] => nil
   | (i,psi)::specs' => if Pos.eqb p i then (i,phi)::specs' else (i,psi)::replace_spec specs' p phi
  end.

Lemma replace_spec_find_id: forall specs p phi i,
  find_id i (replace_spec specs p phi) =
  if Pos.eqb i p then match find_id i specs with None => None | Some _ => Some phi end
  else find_id i specs.
Proof. induction specs; simpl; intros.
  + destruct (Pos.eqb i p); trivial.
  + destruct a.
    remember (Pos.eqb p i0) as b; symmetry in Heqb; destruct b; simpl.
    - apply Peqb_true_eq in Heqb. subst i0.
      remember (Memory.EqDec_ident i p) as b; symmetry in Heqb; destruct b; subst.
      * rewrite Pos.eqb_refl; trivial.
      * remember (Pos.eqb i p) as w; symmetry in Heqw; destruct w; simpl in *; trivial.
        apply Pos.eqb_eq in Heqw. congruence.
    - rewrite IHspecs; clear IHspecs.
      remember (Memory.EqDec_ident i i0) as w; destruct w; symmetry in Heqw; subst; simpl; trivial.
      rewrite Pos.eqb_sym, Heqb; trivial.
Qed.

Lemma replace_spec_map_fst p phi: forall l, map fst (replace_spec l p phi) = map fst l.
Proof.
  induction l; simpl; trivial. destruct a; simpl.
  destruct ((p =? i)%positive); simpl. trivial. rewrite IHl; trivial.
Qed.

Lemma replace_spec_NotFound p phi: forall l (P:~ In p (map fst l)), replace_spec l p phi = l.
Proof. induction l; intros; simpl; trivial. destruct a; simpl in *.
   remember ((p =? i)%positive) as b; destruct b; symmetry in Heqb; simpl.
+ apply Pos.eqb_eq in Heqb; subst. elim P. left; trivial.
+ f_equal. apply IHl; clear IHl. intros N. apply P; clear P. right; trivial.
Qed.

Lemma replace_spec_Forall2_funspec_sub p phi: forall (l : funspecs)
  (LNR: list_norepet (map fst l))
  (Hp: match find_id p l with None => True | Some psi => funspec_sub psi phi end),
  Forall2 funspec_sub (map snd l) (map snd (replace_spec l p phi)).
Proof. induction l; simpl; intros. constructor. inv LNR; destruct a. specialize (IHl H2); simpl.
   remember ((p =? i)%positive) as b; destruct b; symmetry in Heqb; simpl.
+ apply Pos.eqb_eq in Heqb; subst. destruct (Memory.EqDec_ident i i); [| contradiction].
  constructor. trivial.
  simpl in H1. rewrite replace_spec_NotFound in IHl; trivial.
  apply assoclists.find_id_None_iff in H1; rewrite H1 in IHl.
  apply IHl; trivial.
+ destruct (Memory.EqDec_ident p i); subst. apply Pos.eqb_neq in Heqb; contradiction.
  constructor. apply funspec_sub_refl. apply (IHl Hp).
Qed.

Lemma replace_specSome_funspec_sub p phi psi: forall (l : funspecs)
  (LNR: list_norepet (map fst l))
  (Hp: find_id p l = Some psi) (Psi: funspec_sub psi phi),
  Forall2 funspec_sub (map snd l) (map snd (replace_spec l p phi)).
Proof. intros. eapply replace_spec_Forall2_funspec_sub. trivial. rewrite Hp; trivial. Qed.

Lemma Forall2_funspec_sub_refl: forall l, Forall2 funspec_sub l l.
Proof. induction l; constructor; trivial. apply funspec_sub_refl. Qed.

Lemma Forall2_funspec_sub_trans: forall l1 l2 l3, Forall2 funspec_sub l1 l2 -> 
      Forall2 funspec_sub l2 l3 -> Forall2 funspec_sub l1 l3.
Proof.
  induction l1; intros l2 l3 H12 H13; inv H12; inv H13; constructor.
  eapply funspec_sub_trans; eassumption. eauto.
Qed.

Lemma replace_specNone_Forall2_funspec_sub p phi: forall (l : funspecs)
  (Hp: find_id p l = None),
  Forall2 funspec_sub (map snd l) (map snd (replace_spec l p phi)).
Proof. intros. rewrite replace_spec_NotFound. apply Forall2_funspec_sub_refl.
  apply assoclists.find_id_None_iff; trivial.
Qed.

Definition replace_specs:= List.fold_right (fun iphi l=> replace_spec l (fst iphi) (snd iphi)).

Lemma replace_specs_map_fst: forall l specs, map fst (replace_specs specs l) = map fst specs.
Proof. induction l; intros. trivial. simpl; rewrite replace_spec_map_fst; trivial. Qed.

Lemma replace_specs_preserved specs: forall l i (Hi: ~In i (map fst l)),
      find_id i (replace_specs specs l) = find_id i specs.
Proof.
  induction l; simpl; intros. trivial.
  destruct a; simpl in *. rewrite replace_spec_find_id.
  remember ((i =? i0)%positive) as b; symmetry in Heqb; destruct b.
+ apply Peqb_true_eq in Heqb. subst i0. elim Hi. left; trivial.
+ apply IHl. intros N. apply Hi. right; trivial.
Qed.

Lemma weakenExports_condition: forall (l specs:funspecs)(LNRL: list_norepet (map fst l)) (LNRspecs: list_norepet (map fst specs)),
      Forall2 (fun x phi => match x with None => False | Some psi => funspec_sub psi phi end) 
              (map (fun i => find_id i specs) (map fst l)) (map snd l) ->
      Forall2 funspec_sub (map snd specs) (map snd (replace_specs specs l)).
Proof. induction l; simpl; intros. apply Forall2_funspec_sub_refl. 
  destruct a as [i phi]; simpl in *. inv H. inv LNRL. specialize (IHl _ H2 LNRspecs H5); clear H5.
  remember (find_id i specs) as p; symmetry in Heqp; destruct p; [ | contradiction]. 
  eapply Forall2_funspec_sub_trans. apply IHl. clear IHl.
  eapply replace_specSome_funspec_sub.
  rewrite replace_specs_map_fst; trivial.
  rewrite replace_specs_preserved. apply Heqp. trivial.
  trivial.
Qed.

Lemma weakenExports
   {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (newExports: funspecs)
   (L: list_norepet (map fst newExports))
   (HH: Forall2 (fun x phi => match x with Some psi => funspec_sub psi phi | None => False end)
                (map (fun i : ident => find_id i Exports) (map fst newExports)) 
                (map snd newExports)):
   restrictExports v (replace_specs Exports newExports).
Proof.
eapply prove_restrictExports2. apply replace_specs_map_fst.
apply weakenExports_condition; trivial.
destruct v as [G COMP]; apply COMP.
Qed.

Ltac weakenExports :=
 simple apply weakenExports; 
   [apply compute_list_norepet_e; reflexivity || fail "Your restricted Export list has a duplicate function name"
   | 
   ].

Lemma QPprogdefs_GFF {p i fd}:QPprogram_OK p ->  (QP.prog_defs p) ! i = Some (Gfun fd) -> genv_find_func (QPglobalenv p) i fd.
Proof. apply QPfind_funct_ptr_exists. Qed.

Definition relaxImports {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (Imports': funspecs) :=
   @VSU Espec E Imports' p Exports GP.

Lemma prove_relaxImports2
   {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (Imports': funspecs) :
   map fst Imports = map fst Imports' ->
   Forall2 funspec_sub (map snd Imports') (map snd Imports) ->
   relaxImports v Imports'.
Proof.
intros.
destruct v as [G c].
assert (LNR1: list_norepet (map fst (QPvarspecs p) ++ map fst (G ++ Imports'))).
{ rewrite map_app, <- H, <- map_app. apply c. }
exists G.
apply (@Build_Component _ _ _ _ _ _ _ _ (Comp_prog_OK c)); try apply c; auto.
+ rewrite <- H. apply c.
+ intros.
  assert (LNR2: list_norepet (map fst (QPvarspecs p) ++ map fst (Imports' ++ G))).
  { apply list_norepet_append_inv in LNR1; destruct LNR1 as [? [? ?]].
    apply list_norepet_append; trivial.
    + rewrite map_app. apply (list_norepet_append_commut). rewrite <- map_app; trivial.
    + eapply list_disjoint_mono; eauto.
      intros. rewrite map_app. rewrite map_app in H6.  apply in_or_app. apply in_app_or in H6. rewrite or_comm; trivial. }
  eapply SF_ctx_subsumption.
  - eapply (Comp_G_justified c); eassumption.
  - apply (Comp_ctx_LNR c). 
  - apply cspecs_sub_refl.
  - apply QPprogdefs_GFF; trivial. apply c.
  - intros j. red. rewrite 2 semax_prog.make_context_g_char; trivial.
    2: rewrite map_app, H, <- map_app; trivial.
    rewrite 2 make_tycontext_s_find_id, 2 find_id_app_char.
    remember (find_id j Imports) as w; destruct w; symmetry in Heqw.
    * destruct (find_funspec_sub Imports Imports' H H0 _ _ Heqw) as [psi [Psi PSI]].
      apply type_of_funspec_sub in PSI; rewrite Psi, PSI; trivial.
    * apply find_id_None_iff in Heqw. rewrite H in Heqw. apply find_id_None_iff in Heqw. rewrite Heqw.
      destruct (find_id j G); trivial. destruct (find_id j (QPvarspecs p));  trivial.
  - intros. red. remember (find_id j (Imports ++ G) ) as w; destruct w; trivial; symmetry in Heqw. 
    rewrite find_id_app_char; rewrite find_id_app_char in Heqw.
    remember (find_id j Imports) as q; destruct q; symmetry in Heqq.
    * inv Heqw. destruct (find_funspec_sub _ _ H H0 _ _ Heqq) as [psi [Psi PSI]].
      rewrite Psi. eexists; split. reflexivity. apply (funspec_sub_sub_si _ _ PSI).
    * apply find_id_None_iff in Heqq. rewrite H in Heqq. apply find_id_None_iff in Heqq. rewrite Heqq, Heqw.
      eexists; split. reflexivity. apply funspec_sub_si_refl.
+ intros. specialize (Comp_G_Exports c _ _ E0). destruct (find_id i G). trivial.
  intros [psi [Psi PSI]].
  destruct (find_funspec_sub _ _ H H0 _ _ Psi) as [tau [Tau TAU]].
  exists tau; split. trivial. eapply funspec_sub_trans; eauto.
+ apply (Comp_MkInitPred c).
Qed.

Lemma replace_spec_Forall2_funspec_sub2 p phi: forall (l : funspecs)
  (LNR: list_norepet (map fst l))
  (Hp: match find_id p l with None => True | Some psi => funspec_sub phi psi end),
  Forall2 funspec_sub (map snd (replace_spec l p phi)) (map snd l).
Proof. induction l; simpl; intros. constructor. inv LNR; destruct a. specialize (IHl H2); simpl.
   remember ((p =? i)%positive) as b; destruct b; symmetry in Heqb; simpl.
+ apply Pos.eqb_eq in Heqb; subst. destruct (Memory.EqDec_ident i i); [| contradiction].
  constructor. trivial.
  simpl in H1. rewrite replace_spec_NotFound in IHl; trivial.
  apply assoclists.find_id_None_iff in H1; rewrite H1 in IHl.
  apply IHl; trivial.
+ destruct (Memory.EqDec_ident p i); subst. apply Pos.eqb_neq in Heqb; contradiction.
  constructor. apply funspec_sub_refl. apply (IHl Hp).
Qed.

Lemma replace_specSome_funspec_sub2 p phi psi: forall (l : funspecs)
  (LNR: list_norepet (map fst l))
  (Hp: find_id p l = Some psi) (Psi: funspec_sub phi psi),
  Forall2 funspec_sub (map snd (replace_spec l p phi))(map snd l) .
Proof. intros. eapply replace_spec_Forall2_funspec_sub2. trivial. rewrite Hp; trivial. Qed.

Lemma strengthenImports_condition: forall (l specs:funspecs)(LNRL: list_norepet (map fst l)) (LNRspecs: list_norepet (map fst specs)),
      Forall2 (fun phi x => match x with None => False | Some psi => funspec_sub phi psi end) 
               (map snd l) (map (fun i => find_id i specs) (map fst l))->
      Forall2 funspec_sub (map snd (replace_specs specs l)) (map snd specs).
Proof. induction l; simpl; intros. apply Forall2_funspec_sub_refl. 
  destruct a as [i phi]; simpl in *. inv H. inv LNRL. specialize (IHl _ H2 LNRspecs H5); clear H5.
  remember (find_id i specs) as p; symmetry in Heqp; destruct p; [ | contradiction]. 
  eapply Forall2_funspec_sub_trans. 2: apply IHl. clear IHl.
  eapply replace_specSome_funspec_sub2.
  rewrite replace_specs_map_fst; trivial.
  rewrite replace_specs_preserved. apply Heqp. trivial.
  trivial.
Qed.
Lemma strengthenImports
   {Espec E Imports p Exports GP} 
   (v: @VSU Espec E Imports p Exports GP)
   (newImports: funspecs)
   (L: list_norepet (map fst newImports))
   (IdentsEq: map fst newImports = map fst Imports)
   (HH:Forall2 (fun phi x => match x with Some psi => funspec_sub phi psi | None => False end)
               (map snd newImports)
               (map (fun i : ident => find_id i Imports) (map fst Imports))):
   relaxImports v (replace_specs Imports newImports).
Proof.
eapply prove_relaxImports2. rewrite replace_specs_map_fst; trivial.
eapply strengthenImports_condition; trivial. rewrite <- IdentsEq ; trivial.
rewrite IdentsEq. trivial.
Qed.

Ltac strengthenImports :=
 simple apply strengthenImports; 
   [apply compute_list_norepet_e; reflexivity || fail "Your restricted Export list has a duplicate function name"
   | try reflexivity |
   ].

Ltac simplify_VSU_type t :=
 lazymatch t with
 | restrictExports _ _ => let t := eval red in t in simplify_VSU_type t
 | privatizeExports _ _ => let t := eval red in t in simplify_VSU_type t
 | relaxImports _ _ => let t := eval red in t in simplify_VSU_type t
 | VSU _ _ _ _ _ => t
 | _ => fail "The type of this supposed VSU is" t "which might be OK but we hesitate to reduce it for fear of blowup"
 end.

Ltac VSULink_type v1 v2 :=
lazymatch type of v1 with ?t1 => let t1 := simplify_VSU_type t1 in
lazymatch t1 with 
  | @VSU ?Espec ?E1 ?Imports1 ?p1 ?Exports1 ?GP1 =>
lazymatch type of v2 with ?t2 => let t2 := simplify_VSU_type t2 in
lazymatch t2 with 
  | @VSU Espec ?E2 ?Imports2 ?p2 ?Exports2 ?GP2 =>
          let GP := uconstr:((GP1 * GP2)%logic) in
          let E := uconstr:((G_merge E1 E2)) in
          let E := simplify_funspecs E in
          let Imports := compute_VSULink_Imports v1 v2 in
          let Exports := constr:((G_merge Exports1 Exports2)) in
          let Exports := simplify_funspecs Exports in
          let p' := uconstr:((QPlink_progs p1 p2)) in
          let p'' := eval vm_compute in p' in
          let p :=
           lazymatch p'' with
           | Errors.OK ?p =>
               uconstr:(@abbreviate _ p)
           | Errors.Error ?m => fail "QPlink_progs failed:" m
           end
          in
          constr:((@VSU Espec E Imports p Exports GP))
  | _ => fail "Especs of VSUs don't match"
end end end end.

Ltac linkVSUs v1 v2 :=
  let t := VSULink_type v1 v2 in
 match t with @VSU ?Espec ?E ?Imports ?p ?Exports ?GP =>
   apply (VSULink'' Espec _ _ _ _ _ _ _ _ _ _ v1 v2 E Imports p Exports)
  end;
  [ reflexivity | reflexivity | reflexivity | reflexivity
  | reflexivity || fail "Fundefs_match failed"
  | reflexivity || fail "Externs of vsu1 overlap with Internals of vsu2"
  | reflexivity || fail "Externs of vsu2 overlap with Internals of vsu1"
  | SC_tac
  | SC_tac
  | HImports_tac'
  ].

Ltac linkVSUs_Type v1 v2 := let t := VSULink_type v1 v2 in exact t.
Ltac linkVSUs_Body v1 v2 :=
apply (VSULink'' _ _ _ _ _ _ _ _ _ _ _ v1 v2);
   [ reflexivity
   | reflexivity
   | reflexivity
   | reflexivity
   | reflexivity || fail "Fundefs_match failed"
   | reflexivity || fail "Externs of vsu1 overlap with Internals of vsu2"
   | reflexivity || fail "Externs of vsu2 overlap with Internals of vsu1"
   | SC_tac
   | SC_tac
   | HImports_tac' ].

Definition VSU_of_Component {Espec E Imports p Exports GP G}
          (c: @Component Espec (QPvarspecs p) E Imports p Exports GP G) : 
             @VSU Espec E Imports p Exports GP :=
  ex_intro _ G c.

Lemma global_is_headptr g i: isptr (globals_of_env g i) -> headptr (globals_of_env g i).
Proof. unfold globals_of_env, headptr; simpl.
  destruct (Map.get (ge_of g) i); simpl; intros; [ exists b; trivial | contradiction].
Qed.

Lemma align_compatible_tint_tuint {cs b}: @align_compatible cs tint (Vptr b Ptrofs.zero) =
                @align_compatible cs tuint (Vptr b Ptrofs.zero).
Proof.
  unfold align_compatible. apply prop_ext; split; intros.
+ inv H. econstructor. reflexivity. simpl. apply Z.divide_0_r. 
+ inv H. econstructor. reflexivity. simpl. apply Z.divide_0_r.
Qed.

Lemma semax_body_Gmerge1 {cs} V G1 G2 f iphi (SB: @semax_body V G1 cs f iphi)
  (G12: forall i phi1 phi2, find_id i G1 = Some phi1 -> find_id i G2 = Some phi2 ->
        typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
        callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
   (LNR: list_norepet (map fst V ++ map fst (G_merge G1 G2))):
   @semax_body V (G_merge G1 G2) cs f iphi.
Proof. 
assert (LNR_VG1: list_norepet (map fst V ++ map fst G1)). 
{ clear - LNR. apply list_norepet_append_inv in LNR; destruct LNR as [? [? ?]].
  apply list_norepet_append; trivial.
  + rewrite (@G_merge_dom G1 G2), map_app in H0.
    apply list_norepet_append_inv in H0; apply H0.
  + eapply list_disjoint_mono. apply H1. 2: trivial.
    intros. rewrite (@G_merge_dom G1 G2), map_app. apply in_or_app. left; trivial. }
assert (LNR_G1: list_norepet (map fst G1)). 
{ clear - LNR_VG1. apply list_norepet_append_inv in LNR_VG1; apply LNR_VG1. }
assert (D1: forall j t, find_id j V = Some t -> find_id j G1 = None).
{ clear - LNR. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  rewrite (@G_merge_dom G1 G2), map_app. apply in_or_app. left; trivial. }
assert (D2: forall j t, find_id j V = Some t -> find_id j G2 = None).
{ clear - LNR LNR_G1. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  apply G_merge_InDom; trivial.
  destruct (in_dec ident_eq j (map fst G1)). left; trivial. right; split; trivial. }
eapply semax_body_subsumespec. eassumption.
2: intros; apply subsumespec_G_merge_l; eauto.
intros. red. specialize (D1 i); specialize (D2 i).
remember (find_id i V) as q; destruct q; symmetry in Heqq. 
+ erewrite 2 semax_prog.make_context_g_mk_findV_mk; try eassumption.
  trivial.
+ remember ((make_tycontext_g V G1) ! i) as w; symmetry in Heqw; destruct w; trivial.
  specialize (G12 i).
  remember (find_id i G1) as a; symmetry in Heqa; destruct a.
  - erewrite semax_prog.make_tycontext_s_g in Heqw.
    2:  rewrite make_tycontext_s_find_id; eassumption. 
    inv Heqw.
    remember (find_id i G2) as b; symmetry in Heqb; destruct b.
    * destruct (G12 _ _ (eq_refl _) (eq_refl _)); clear G12.
      destruct (G_merge_find_id_SomeSome Heqa Heqb H H0) as [psi [Psi PSI]].
      apply funspectype_of_binary_intersection in Psi; destruct Psi.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      rewrite H1; trivial. 
    * apply (G_merge_find_id_SomeNone Heqa) in Heqb.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      trivial.
  - rewrite (semax_prog.make_tycontext_g_G_None _ _ _ Heqa) in Heqw; congruence.
Qed.

Lemma semax_body_Gmerge2 {cs} V G1 G2 f iphi (SB:@semax_body V G2 cs f iphi)
  (G12: forall i phi1 phi2, find_id i G1 = Some phi1 -> find_id i G2 = Some phi2 ->
        typesig_of_funspec phi1 = typesig_of_funspec phi2 /\
        callingconvention_of_funspec phi1 = callingconvention_of_funspec phi2)
   (LNR_VG1: list_norepet (map fst V ++ map fst G1)) 
   (LNR_VG2: list_norepet (map fst V ++ map fst G2)):
   @semax_body V (G_merge G1 G2) cs f iphi.
Proof.
assert (LNR: list_norepet (map fst V ++ map fst (G_merge G1 G2))).
{ apply list_norepet_append_inv in LNR_VG1; destruct LNR_VG1 as [? [? ?]].
  apply list_norepet_append_inv in LNR_VG2; destruct LNR_VG2 as [? [? ?]].
  apply list_norepet_append; trivial.
  + apply G_merge_LNR; trivial.
  + intros ? ? ? ?. apply G_merge_InDom in H6; trivial.
    destruct H6 as [Y | [YY Y]]. apply H1; trivial. apply H4; trivial. }
assert (LNR_G1: list_norepet (map fst G1)). 
{ clear - LNR_VG1. apply list_norepet_append_inv in LNR_VG1; apply LNR_VG1. }
assert (D1: forall j t, find_id j V = Some t -> find_id j G1 = None).
{ clear - LNR. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  rewrite (@G_merge_dom G1 G2), map_app. apply in_or_app. left; trivial. }
assert (D2: forall j t, find_id j V = Some t -> find_id j G2 = None).
{ clear - LNR LNR_G1. intros.
  apply (@list_norepet_find_id_app_exclusive1 _ _ _ _ LNR) in H.
  apply find_id_None_iff. apply find_id_None_iff in H. intros N; apply H; clear H.
  apply G_merge_InDom; trivial.
  destruct (in_dec ident_eq j (map fst G1)). left; trivial. right; split; trivial. }
assert (LNR_G2: list_norepet (map fst G2)). 
{ clear - LNR_VG2. apply list_norepet_append_inv in LNR_VG2; apply LNR_VG2. }

eapply semax_body_subsumespec. eassumption.
2: intros; apply subsumespec_G_merge_r; eauto.
intros. red. specialize (D1 i); specialize (D2 i).
remember (find_id i V) as q; destruct q; symmetry in Heqq. 
+ erewrite 2 semax_prog.make_context_g_mk_findV_mk; try eassumption.
  trivial.
+ remember ((make_tycontext_g V G2) ! i) as w; symmetry in Heqw; destruct w; trivial.
  specialize (G12 i).
  remember (find_id i G2) as a; symmetry in Heqa; destruct a.
  - erewrite semax_prog.make_tycontext_s_g in Heqw.
    2:  rewrite make_tycontext_s_find_id; eassumption. 
    inv Heqw.
    remember (find_id i G1) as b; symmetry in Heqb; destruct b.
    * destruct (G12 _ _ (eq_refl _) (eq_refl _)); clear G12.
      destruct (G_merge_find_id_SomeSome Heqb Heqa H H0) as [psi [Psi PSI]].
      apply funspectype_of_binary_intersection in Psi; destruct Psi.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      rewrite H2; trivial. 
    * apply (G_merge_find_id_NoneSome Heqb) in Heqa; trivial.
      erewrite semax_prog.make_tycontext_s_g.
      2: rewrite make_tycontext_s_find_id; eassumption.
      trivial.
  - rewrite (semax_prog.make_tycontext_g_G_None _ _ _ Heqa) in Heqw; congruence.
Qed.

Lemma globs_to_globvars:
 forall prog rho, 
  Forall (fun ig => isptr (globals_of_env rho (fst ig))) (QPprog_vars prog) ->
 globvars2pred (globals_of_env rho) (QPprog_vars prog)
  |-- InitGPred (Vardefs prog) (globals_of_env rho).
Proof.
intros.
unfold globvars2pred.
unfold QPprog_vars, Vardefs in *.
induction (PTree.elements (QP.prog_defs prog)).
simpl.
apply derives_refl.
simpl.
destruct a.
unfold isGvar.
simpl.
destruct g; simpl.
simpl in H.
apply IHl; auto.
rewrite InitGPred_consD.
simpl in H. inv H.
simpl in H2.
apply sepcon_derives; auto.
clear IHl.
unfold globs2pred, globvar2pred.
simpl.
rewrite prop_true_andp by (apply global_is_headptr; auto).
destruct (gvar_volatile v).
apply derives_refl.
clear H3 H2.
forget (globals_of_env rho p) as g.
change (initialize.readonly2share (gvar_readonly v))
  with (readonly2share (gvar_readonly v)).
forget (readonly2share (gvar_readonly v)) as sh.
revert g; induction (gvar_init v); intros; simpl; auto.
Qed.

Definition main_pre {Z: Type} (prog: QP.program function) (ora: Z) : globals -> argsEnviron -> mpred :=
 (fun gv rho => 
  !! (gv = initialize.genviron2globals (fst rho) /\ snd rho = []) &&
   (globvars2pred gv (QPprog_vars prog) * has_ext ora))%logic.

Definition main_pre_old {Z : Type} (prog : QP.program function) (ora : Z) 
  (gv : globals) (rho : environ) :=
 !! (gv = globals_of_env rho) &&
   (globvars2pred gv (QPprog_vars prog) * has_ext ora)%logic.

Lemma main_pre_InitGpred:
 forall globs (Espec: OracleKind) (cs: compspecs)  Delta prog1 prog2 Z (ext:Z) (gv: globals) R c Post
  (H1: globals_ok gv -> InitGPred (Vardefs prog1) gv |-- globs)
  (H: Vardefs prog1 = Vardefs prog2)
  (H0: Forall (fun ig : ident * _ => isSome ((glob_types Delta) ! (fst ig))) (QPprog_vars prog2))
  (H2: semax Delta (sepcon (PROP ( )  LOCAL (gvars gv)  SEP (globs; has_ext ext)) R) c Post),
  semax Delta (sepcon (close_precondition nil (@main_pre Z prog2 ext gv)) R) c Post.
Proof.
intros.
rewrite H in H1. clear H prog1. rename H1 into H.
eapply semax_pre; [ | apply H2]; clear H2.
unfold main_pre, PROPx, LOCALx, SEPx, local, lift1.
intro rho.
unfold close_precondition.
simpl. unfold_lift.
normalize.
clear H2 H3.
rewrite prop_true_andp.
2:{ split; auto. hnf. reflexivity. }
apply sepcon_derives; auto.
apply sepcon_derives; auto.
eapply derives_trans; [ | apply H]; clear H.
2:{
clear. intro i.
unfold initialize.genviron2globals.
destruct (Map.get (ge_of rho) i); auto.
left; eexists; eauto.
}
unfold Vardefs, InitGPred.
unfold SeparationLogic.prog_vars.
clear - H0 H1.
unfold QPprog_vars in *.
induction (PTree.elements (QP.prog_defs prog2)); simpl.
auto.
destruct a.
simpl in H0.
destruct g; simpl; auto.
inv H0.
apply sepcon_derives; auto.
rewrite prop_true_andp; auto.
clear - H1 H3.
destruct H1 as [_ [_ ?]].
simpl in *.
specialize (H p).
destruct ((glob_types Delta) ! p); inv H3.
specialize (H _ (eq_refl _)) as [b ?].
unfold initialize.genviron2globals.
rewrite H.
exists b; auto.
Qed.



Lemma VSU_MkInitPred {Espec E Imports p Exports GP} 
  (vsu: @VSU Espec E Imports p Exports GP) 
  (gv: globals) : globals_ok gv -> InitGPred (Vardefs p) gv |-- (GP gv).
Proof.
intros. destruct vsu as [G comp].
apply (Comp_MkInitPred comp); auto.
Qed.

Ltac report_failure :=
 match goal with |- ?G => fail 99 "expand_main_pre_new failed with goal" G end.

Ltac unfold_all R :=
 match R with
 | sepcon ?a ?ar => let b := unfold_all a in
                      let br := unfold_all ar in
                      constr:(sepcon b br)
 | ?a => let x := eval unfold a in a in unfold_all x
 | ?a => constr:(a)
 end.

Ltac expand_main_pre_VSU :=
  lazymatch goal with
  | vsu: VSU _ _ _ _ _ |- _ => 
    (eapply main_pre_InitGpred || report_failure); 
        [ try apply (VSU_MkInitPred vsu); report_failure
        | try (unfold Vardefs; simpl; reflexivity); report_failure
        | try solve [repeat constructor]; report_failure
        |  ];
     clear vsu;
     match goal with
      |- semax _ (PROPx _ (LOCALx _ (SEPx (?R _ :: _))) * _)%logic _ _ =>
        let x := unfold_all R in change R with x
     end;
     repeat change ((sepcon ?A ?B) ?gv) with (sepcon (A gv) (B gv));
     change (emp ?gv) with (@emp mpred _ _);
     rewrite ?emp_sepcon, ?sepcon_emp;
     repeat match goal with |- semax _ (sepcon ?PQR _) _ _ => flatten_in_SEP PQR end
  | |- _ => expand_main_pre_old
  end.

Ltac expand_main_pre ::= 
   expand_main_pre_VSU.

Ltac start_function2 ::=
  first [ erewrite compute_close_precondition_eq; [ | reflexivity | reflexivity]
        | rewrite close_precondition_main
        | match goal with |- semax (func_tycontext _ ?V ?G _) 
              (close_precondition _ (main_pre _ _ _) * _)%logic _ _ =>
                  let x := eval hnf in V in let x := eval simpl in x in change V with x 
          end
        ].

Fixpoint vardefs_to_globvars (vdefs: list (ident * globdef (fundef function) type)) :
    list (ident * globvar type) :=
 match vdefs with
 | (i, Gfun _)::r => vardefs_to_globvars r
 | (i, Gvar v)::r => (i,v) :: vardefs_to_globvars r
 | nil => nil
 end.

Definition vardefs_tycontext (vdefs: list (ident * globdef (fundef function) type)) : tycontext :=
  make_tycontext nil nil nil Tvoid 
   (map (fun iv => (fst iv, gvar_info (snd iv))) (vardefs_to_globvars vdefs))
  nil nil.



Lemma InitGPred_process_globvars:
  forall Delta al gv (R: globals -> mpred),
  Delta = vardefs_tycontext al ->
  ENTAIL Delta, globvars_in_process gv nil emp (vardefs_to_globvars al) |-- lift0 (R gv) ->
  globals_ok gv ->
  InitGPred al gv |-- R gv.
Proof.
intros until 2. intro Hgv; intros.
unfold globvars_in_process in H0.
simpl fold_right_sepcon in H0.
rewrite sepcon_emp, emp_sepcon in H0. 
pose (rho := 
 mkEnviron 
  (fun i => match gv i with Vptr b _ => Some b | _ => None end)
  (Map.empty (block * type))
  (Map.empty val)).
eapply derives_trans; [ | apply (H0 rho)].
clear R H0; subst Delta.
unfold local, lift1.
simpl.
normalize.
subst rho.
unfold tc_environ, typecheck_environ.
simpl.
rewrite prop_and.
rewrite <- and_assoc.
rewrite prop_and.
rewrite prop_true_andp.
-
apply andp_right.
*
apply derives_trans with
(!! (Forall (fun x : (ident * globdef (fundef function) type) => let (i, d) := x in
      match d with Gfun _ => True | Gvar v => headptr (gv i) end) al)).
+
apply derives_trans with (TT * InitGPred al gv)%logic. cancel.
induction al.
apply prop_right; constructor.
rewrite InitGPred_consD.
unfold globs2pred.
destruct a. destruct g.
rewrite emp_sepcon; auto.
eapply derives_trans; [apply IHal |].
apply prop_derives. intros. constructor; auto.
normalize.
rewrite <- sepcon_assoc.
eapply derives_trans; [ eapply derives_trans; [ | apply IHal] | ].
cancel.
clear IHal.
apply prop_derives.
intros. constructor; auto.
+
apply andp_right; apply prop_derives; intros.
 --
induction al; simpl.
hnf; intros. rewrite PTree.gempty in H0; inv H0.
inv H.
specialize (IHal H3). clear H3.
destruct a. destruct g.
auto.
simpl.
intros ? ?.
specialize (IHal id t).
intros.
destruct (eq_dec id i).
subst id.
rewrite PTree.gss in H.
inv H.
unfold Map.get.
destruct H2. rewrite H. eauto.
rewrite PTree.gso in H by auto.
specialize (IHal H).
destruct IHal as [b ?]; exists b.
unfold Map.get in *.
destruct (Memory.EqDec_ident i id); try congruence.
 --
unfold gvars_denote.
simpl ge_of.
extensionality i.
unfold Map.get.
specialize (Hgv i).
destruct Hgv as [[b' Hgv] | Hgv];
rewrite Hgv; auto.
*
induction al; simpl. 
rewrite InitGPred_nilD. auto.
rewrite InitGPred_consD.
rewrite fold_right_map in IHal.
rewrite fold_right_map.
destruct a. destruct g.
simpl. rewrite emp_sepcon; auto.
simpl.
normalize.
apply sepcon_derives; auto.
-
split.
hnf; intros. rewrite PTree.gempty in H; inv H.
hnf; intros.
split; intros. rewrite PTree.gempty in H; inv H.
destruct H. unfold Map.get, Map.empty in H.  inv H. 
Qed.

Lemma finish_process_globvars' :
 forall gv (done: list mpred) (R: mpred), 
  fold_right_sepcon done |-- R -> 
globvars_in_process gv done emp nil |-- lift0 R.
Proof.
intros.
intro rho.
unfold globvars_in_process, globvars2pred, lift0. simpl.
normalize.
Qed.

Lemma globals_ok_isptr_headptr:
  forall gv i, globals_ok gv -> isptr (gv i) -> headptr (gv i).
Proof.
intros.
destruct (H i); auto.
rewrite H1 in H0; contradiction.
Qed.

#[export] Hint Resolve globals_ok_isptr_headptr: core.

Lemma globals_ok_genviron2globals:
  forall g,  globals_ok (initialize.genviron2globals g).
Proof.
intros. intro i; simpl. unfold initialize.genviron2globals.
destruct (Map.get g i); auto.
left; eexists; eauto.
Qed.

#[export] Hint Resolve globals_ok_genviron2globals : core.

Definition VSU_initializer {cs: compspecs} (prog: Clight.program) (Gpred: globals -> mpred) :=
 forall gv, globals_ok gv -> InitGPred (Vardefs (QPprog prog)) gv |-- Gpred gv.

Ltac InitGPred_tac :=
intros ? ?;
eapply InitGPred_process_globvars; auto;
let Delta := fresh "Delta" in let Delta' := fresh "Delta'" in 
set (Delta' := vardefs_tycontext _);
set (Delta := @abbreviate tycontext Delta');
change Delta' with Delta;
hnf in Delta'; simpl in Delta'; subst Delta';
simpl vardefs_to_globvars;
try match goal with |- context [PTree.prev ?A] =>
  let a := constr:(PTree.prev A) in let a := eval compute in a in
    change (PTree.prev A) with a end;
eapply derives_trans; [process_globals | ];
clear Delta;
apply finish_process_globvars'; unfold fold_right_sepcon at 1;
repeat change_mapsto_gvar_to_data_at.

Definition QPprog' {cs: compspecs} 
  {comps: list composite_definition}
  {defs: list (prod ident (globdef Clight.fundef type))}
  {pubs: list ident}
  {main: ident}
  {comps_OK: wf_composites comps}
  (prog: Clight.program)
  (H: prog = Clightdefs.mkprogram comps defs pubs main comps_OK)
  (H0: cenv_built_correctly comps (@cenv_cs cs) = Errors.OK tt)
 : QP.program function :=
 QP.Build_program _ (filter_options is_builtin defs)
  (PTree_Properties.of_list (filter not_builtin defs))
  pubs main
  (QPcomposite_env_of_composite_env 
    (@cenv_cs cs) (@ha_env_cs cs) (@la_env_cs cs)).

Lemma QPprog'_eq:
  forall {cs: compspecs} 
  {comps: list composite_definition}
  {defs: list (prod ident (globdef Clight.fundef type))}
  {pubs: list ident}
  {main: ident}
  {comps_OK: wf_composites comps}
  (prog: Clight.program)
  (H: prog = Clightdefs.mkprogram comps defs pubs main comps_OK)
  (H0: cenv_built_correctly comps (@cenv_cs cs) = Errors.OK tt),
 QPprog' prog H H0 = QPprog prog.
Proof.
intros.
unfold QPprog',QPprog.
unfold QPprogram_of_program.
assert (prog_defs prog = defs)
  by (subst prog; rewrite prog_defs_Clight_mkprogram; auto).
rewrite H1.
f_equal.
rewrite H.
unfold Clightdefs.mkprogram.
destruct (build_composite_env' comps comps_OK). reflexivity.
rewrite H.
unfold Clightdefs.mkprogram.
destruct (build_composite_env' comps comps_OK). reflexivity.
f_equal.
subst prog.
apply extract_compEnv.
apply cenv_built_correctly_e; auto.
Qed.

Ltac QPprog p :=
  tryif (let p' := eval cbv delta [p] in p in
          match p' with Clightdefs.mkprogram _ _ _ _ _ => idtac end)
  then (let a := constr:(QPprog' p (eq_refl _)) in
           (let q := constr:(a (eq_refl _)) in
            let q := eval hnf in q in
            let q := eval simpl in q in
            exact (@abbreviate _ q))
          || match type of a with ?e -> _ =>
                 let e := eval hnf in e in
                 let e :=eval simpl in e in
                 lazymatch e with
                 | Errors.OK _ => fail 0 "impossible error in QPprog'"
                 | Errors.Error ?m => fail 0 m
                 end
                end)
  else (idtac "Remark: QPprog alternate path!";
         let q := constr:(QPprog p) in 
         let q := eval hnf in q in
         let q := eval simpl in q in
         exact (@abbreviate _ q)).

Lemma wholeprog_varspecsJoin:
 forall p1 p2 p, 
 QPlink_progs p1 p2 = Errors.OK p ->
  varspecsJoin (QPvarspecs p) (QPvarspecs p2) (QPvarspecs p).
Proof.
intros.
apply QPlink_progs_globdefs in H.
intro i.
apply (merge_PTrees_e i) in H.
destruct (find_id i (QPvarspecs p)) eqn:?H.
apply find_id_QPvarspecs in H0. destruct H0 as [? [? ?]].
subst t.
rewrite H0 in H.
destruct (find_id i (QPvarspecs p2)) eqn:?H.
apply find_id_QPvarspecs in H1. destruct H1 as [? [? ?]].
subst t.
rewrite H1 in H.
split; auto.
destruct ((QP.prog_defs p1) ! i).
destruct H as [? [? ?]]. destruct g; inv H. destruct f; inv  H4.
destruct v,x0; inv H4.
inv H; auto.
auto.
destruct (find_id i (QPvarspecs p2)) eqn:?H; auto.
apply find_id_QPvarspecs in H1. destruct H1 as [? [? ?]].
subst t.
rewrite H1 in *.
destruct ((QP.prog_defs p1) ! i) eqn:?H.
destruct H as [? [? ?]].
destruct g as [[|]|]; inv H.
destruct v,x; inv H5.
rewrite (proj2 (find_id_QPvarspecs p i (gvar_info x))) in H0.
inv H0.
eauto.
Qed.

Lemma prove_sub_option_find_id:
 forall {A} (G1 G2: list (ident*A)),
  Forall (fun ix => find_id (fst ix) G2 = Some (snd ix)) G1 ->
  forall i, sub_option (find_id i G1) (find_id i G2).
Proof.
intros.
red.
destruct (find_id i G1) eqn:?H; auto.
induction G1 as [|[j?]]; simpl in *; auto.
inv H0.
inv H.
simpl in *.
if_tac in H0. subst j. inv H0. auto.
auto.
Qed.

Definition Comp_GP {Espec V E Imports p Exports GP G} 
  (c: @Component Espec V E Imports p Exports GP G) := GP.

Lemma ComponentJoin':
 forall
  {Espec V1 E1 Imports1 p1 Exports1 GP1 G1} 
     (c1: @Component Espec V1 E1 Imports1 p1 Exports1 GP1 G1)
  {V2 E2 Imports2 p2 Exports2 GP2 G2}
     (c2: @Component Espec V2 E2 Imports2 p2 Exports2 GP2 G2)
  V E Imports p Exports GP G,
  QPlink_progs p1 p2 = Errors.OK p ->
       list_norepet (map fst V) ->
      varspecsJoin V1 V2 V ->
       list_disjoint (map fst V1)
         (map fst E2 ++ map fst Imports2 ++ IntIDs p2) ->
       list_disjoint (map fst V2)
         (map fst E1 ++ map fst Imports1 ++ IntIDs p1) ->
       Fundefs_match p1 p2 Imports1 Imports2 ->
       list_disjoint (map fst E1) (IntIDs p2) ->
       list_disjoint (map fst E2) (IntIDs p1) ->
       (forall (i : ident) (phiI : funspec),
        initial_world.find_id i Imports2 = Some phiI ->
        In i (map fst E1 ++ IntIDs p1) ->
        exists phiE : funspec,
          initial_world.find_id i Exports1 = Some phiE /\
          funspec_sub phiE phiI) ->
       (forall (i : ident) (phiI : funspec),
        initial_world.find_id i Imports1 = Some phiI ->
        In i (map fst E2 ++ IntIDs p2) ->
        exists phiE : funspec,
          initial_world.find_id i Exports2 = Some phiE /\
          funspec_sub phiE phiI) ->
       (forall (i : ident) (phi1 phi2 : funspec),
        initial_world.find_id i Imports1 = Some phi1 ->
        initial_world.find_id i Imports2 = Some phi2 ->
        phi1 = phi2) ->
     E = G_merge E1 E2 ->
     Imports = JoinedImports E1 Imports1 E2 Imports2 p1 p2 ->
     Exports = G_merge Exports1 Exports2 ->
     GP = (GP1 * GP2)%logic ->
     G = G_merge (Comp_G c1) (Comp_G c2) ->
  @Component Espec V E Imports p Exports GP G.
Proof.
intros.
subst.
apply ComponentJoin; auto.
Qed.

Ltac QPlink_progs p1 p2 :=
  let p' :=  constr:(QPlink_progs  p1 p2) in
  let p'' := eval vm_compute in p' in
  let p := lazymatch p'' with
               | Errors.OK ?p => constr:(@abbreviate _ p)
               | Errors.Error ?m => fail "QPlink_progs failed:" m
               end in
  exact p.

Definition matchImportExport (p: QP.program function) (ix: ident * funspec) : bool :=
  match (QP.prog_defs p) ! (fst ix) with
  | Some (Gfun (External _ _ _ _)) => true
  | _ => false
  end.

Definition MainCompType 
   (mainE: funspecs)
   (main_prog: QP.program function)
   {Espec coreE coreprog coreExports coreGP}
   (coreVSU: @VSU Espec coreE nil coreprog coreExports coreGP)
   (whole_prog: QP.program function)
   (main_spec: funspec)
   GP :=
   @Component Espec (QPvarspecs whole_prog) mainE 
             (filter (matchImportExport main_prog) (VSU_Exports coreVSU))
             main_prog [(QP.prog_main main_prog, main_spec)] GP [(QP.prog_main main_prog, main_spec)].
(*
Definition WholeCompType 
   {Espec coreE coreprog coreExports coreGP}
   (coreVSU: @VSU Espec coreE nil coreprog coreExports coreGP)
   {mainE mainprog whole_prog main_spec mainGP} 
   (mainComponent: MainCompType mainE mainprog coreVSU whole_prog main_spec mainGP)
 := 
  exists G,
  @Component Espec (QPvarspecs whole_prog) (G_merge mainE coreE) nil whole_prog [(QP.prog_main mainprog, main_spec)]
    (mainGP * coreGP)%logic (G_merge [(QP.prog_main mainprog, main_spec)] G).
*)
Definition WholeCompType 
   {Espec coreE coreprog coreExports coreGP}
   (coreVSU: @VSU Espec coreE nil coreprog coreExports coreGP)
   {mainE mainprog whole_prog main_spec mainGP} 
   (mainComponent: MainCompType mainE mainprog coreVSU whole_prog main_spec mainGP)
 := 
  exists G,
  find_id (QP.prog_main whole_prog) G = None /\
  @Component Espec (QPvarspecs whole_prog) (G_merge mainE coreE) nil whole_prog [(QP.prog_main mainprog, main_spec)]
    (mainGP * coreGP)%logic (G_merge [(QP.prog_main mainprog, main_spec)] G).

Lemma QPlink_progs_main:
  forall p1 p2 p, QPlink_progs p1 p2 = Errors.OK p ->
 QP.prog_main p1 = QP.prog_main p /\
 QP.prog_main p2 = QP.prog_main p.
Proof.
intros.
unfold QPlink_progs in H.
Errors.monadInv H.
destruct (eqb_ident (QP.prog_main p1) (QP.prog_main p2)) eqn:?H; inv EQ3.
simpl.
apply eqb_ident_spec in H. split; auto.
Qed.

Lemma WholeComponent
   {Espec coreE coreprog coreExports coreGP}
   (coreVSU: @VSU Espec coreE nil coreprog coreExports coreGP)
   {mainE mainprog whole_prog main_spec mainGP} 
   (mainComponent: MainCompType mainE mainprog coreVSU whole_prog main_spec mainGP)
   (Linked: QPlink_progs mainprog coreprog = Errors.OK whole_prog)
   (Disj1: list_disjoint (map fst (QPvarspecs coreprog))
           (map fst mainE ++ map fst (VSU_Exports coreVSU) ++ IntIDs mainprog))
   (FDM: Fundefs_match mainprog coreprog (VSU_Exports coreVSU) [])
   (Disj2: list_disjoint (map fst mainE) (IntIDs coreprog))
   (Disj3: list_disjoint (map fst coreE) (IntIDs mainprog))
   (NOimports: [] = JoinedImports mainE (VSU_Exports coreVSU) coreE [] mainprog coreprog)
   (Hmain: id_in_list (QP.prog_main whole_prog)
                      (map fst coreExports ++ IntIDs coreprog ++ map fst coreE) = false):
   WholeCompType coreVSU mainComponent.
Proof.
destruct coreVSU as [coreG coreC].
exists coreG.
split. {
 rewrite find_id_None_iff.
 rewrite <- (Comp_G_dom coreC).
 apply id_in_list_false in Hmain.
 contradict Hmain. apply in_app; right; auto.
}
eapply Comp_Exports_sub2;
 [ apply (ComponentJoin' mainComponent coreC) | | ].
- apply Linked.
- apply QPvarspecs_norepet.
- apply wholeprog_varspecsJoin with (Comp_prog mainComponent); auto.
- simpl.
   apply assoclists.list_disjoint_app_R.
  +
   intros i j ? ? ?; subst j.
   destruct (Comp_Externs coreC _ H0) as [? [? [? [? ?]]]]; clear H0.
   apply list_in_map_inv in H. destruct H as [[j ?] [? ?]]. simpl in *; subst j.
   apply find_id_i in H0; [ | apply QPvarspecs_norepet].
   apply find_id_QPvarspecs in H0. destruct H0 as [? [? ?]]; subst.
   apply QPlink_progs_globdefs in Linked.
   apply (merge_PTrees_e i) in Linked.
   rewrite H1 in Linked. clear H1.
   destruct ((QP.prog_defs mainprog) ! i) eqn:?H.
   destruct Linked as [? [? ?]]. destruct g as [[?|?]|?]; inv H1.
   revert H4; simple_if_tac; intros; inv  H4. congruence.
   revert H4; simple_if_tac; intros; inv  H4. congruence.
   congruence.
  +
   intros i j ? ? ?; subst j.
   apply QPlink_progs_globdefs in Linked.
   apply (merge_PTrees_e i) in Linked.
   apply IntIDs_elim in H0. destruct H0.
   apply PTree.elements_complete in H0.
   rewrite H0 in Linked. clear H0.
   apply list_in_map_inv in H. destruct H as [[j ?] [? ?]]. simpl in *; subst j.
   apply find_id_i in H0; [ | apply QPvarspecs_norepet].
   apply find_id_QPvarspecs in H0. destruct H0 as [? [? ?]]; subst.
   rewrite H in Linked; clear H.
   destruct ((QP.prog_defs mainprog) ! i) eqn:?H.
   destruct Linked as [? [? ?]]. destruct g as [[?|?]|?]; inv H1.
   simpl in H0.
   revert H0; simple_if_tac; intros; inv  H0.
   simpl in H0.
   revert H0; simple_if_tac; intros; inv  H0.
   inv H0.
   inv Linked.
- intros i j ? ? ?.
   apply (Disj1 i j); auto.
   clear - H0.
   rewrite in_app in H0|-*.
   destruct H0; [left|right]; auto.
   rewrite in_app in H|-*.
   destruct H; [left|right]; auto.
   apply In_map_fst_filter3 in H; auto.
- 
   clear - FDM.
   intros i fd1 fd2 H1 H2; specialize (FDM i fd1 fd2 H1 H2).
   destruct fd1; auto. destruct fd2; auto.
   destruct FDM as [phi1 ?]; exists phi1.
   rewrite find_id_filter_char by apply (Comp_Exports_LNR coreC).
   rewrite H. unfold matchImportExport. simpl.
   rewrite H1; auto.
- apply Disj2.
- apply Disj3.
- intros. inv H.
- intros.
    simpl in H.
   apply find_id_filter_Some in H;
       [ | apply (Comp_Exports_LNR coreC)].
   destruct H as [? _]. eexists phiI. split; auto.
   apply funspec_sub_refl.
- intros. inv H0.
- reflexivity.
- symmetry in NOimports |- *.
   unfold JoinedImports in *.
   change (filter _ nil) with (@nil (ident*funspec)) in *.
   rewrite <- app_nil_end in *.
   match goal with |- filter ?A (filter ?B ?C) = _ => forget A as F; forget B as G; forget C as al end.
   clear - NOimports.
   induction al as [|[i?]]; auto.
   simpl in *.
   destruct (G (i,f)). simpl. destruct (F (i,f)); auto.
   inv NOimports. destruct (F (i,f)); auto. inv NOimports.
- reflexivity.
- reflexivity.
- reflexivity.
- repeat constructor. intro Hx; inv Hx.
- intros.
   unfold sub_option.
   destruct main_spec as [main fs].
   simpl.
   if_tac; auto.
   f_equal.
   unfold merge_specs.
   replace (find_id _ _) with (@None funspec); auto.
   symmetry. rewrite find_id_None_iff. 
   apply id_in_list_false in Hmain; contradict Hmain.
   apply in_app. left.
   destruct (QPlink_progs_main _ _ _ Linked).
   rewrite <- H0; auto.
Qed.

(*** proving semax_prog *)

Definition not_builtin' ix := @not_builtin function (fst ix, Gfun (snd ix)).

Definition just_the_right_funspec (G: funspecs)
  (ix: ident * fundef Clight.function) : ident * funspec :=
 (fst ix, match find_id (fst ix) G with
         | Some fs => fs
         | None => vacuous_funspec (snd ix)
         end).


Definition isGfun (ix: ident * globdef (fundef function) type) := match snd ix with Gfun _ => true | _ => false end.

Definition QPall_initializers_aligned (p: QP.program Clight.function) : bool :=
  forallb
  (fun idv : ident * globvar type =>
   (initializers_aligned 0 (gvar_init (snd idv)) &&
    (init_data_list_size (gvar_init (snd idv)) <? Ptrofs.modulus))%bool)
  (QPprog_vars p).

Definition QPmain_spec_ext' {Z} (prog: QP.program function) (ora: Z)
(post: (ident->val) -> environ -> mpred): funspec :=
NDmk_funspec (nil, tint) cc_default (ident->val) (main_pre prog ora) post.

Definition wholeprog_of_QPprog (p: QP.program function) 
              (OK: QPprogram_OK p) 
              (J1: build_composite_env
      (map compdef_of_compenv_element
         (sort_rank (PTree.elements (QP.prog_comp_env p)) [])) =
    Errors.OK
      (composite_env_of_QPcomposite_env (QP.prog_comp_env p)
         (projT1 (proj2 OK)))) 
 :=  {| prog_defs := (map of_builtin p.(QP.prog_builtins)) ++ PTree.elements p.(QP.prog_defs);
    prog_public := p.(QP.prog_public);
    prog_main := p.(QP.prog_main);
    prog_types := map compdef_of_compenv_element 
                             (sort_rank (PTree.elements (p.(QP.prog_comp_env))) nil);
    prog_comp_env := composite_env_of_QPcomposite_env p.(QP.prog_comp_env) 
                                       (projT1 (proj2 OK));
    prog_comp_env_eq := J1
 |}.

Lemma prog_funct'_app:
  forall {F V} al bl, @prog_funct' F V al ++ SeparationLogic.prog_funct' bl = 
                  prog_funct' (al++bl).
Proof.
intros.
induction al as [|[i ?]]; simpl; auto.
destruct g. simpl; f_equal; auto.
auto.
Qed.

Lemma delete_id_Some:
  forall {A} i (al: list (ident * A)) x al',
     list_norepet (map fst al) ->
    delete_id i al = Some (x,al') <-> In (i,x) al /\ al' = filter (negb oo eqb_ident i oo fst) al.
Proof.
induction al as [|[j?]]; simpl; intros.
split; intros. inv H0. destruct H0; contradiction.
inv H.
if_tac. subst j.
split; intros. inv H. split; auto.
rewrite eqb_ident_true. simpl.
rewrite filter_redundant; auto.
intros [j ?] ?.
apply (in_map fst) in H. simpl in H.
simpl. rewrite eqb_ident_false; auto. intro; subst; contradiction.
destruct H.
rewrite eqb_ident_true in H0. simpl in H0.
rewrite filter_redundant in H0.
destruct H. inv H; auto.  
apply (in_map fst) in H. simpl in H. contradiction.
intros [j ?] ?. simpl. rewrite eqb_ident_false; auto. intro; subst.
apply (in_map fst) in H1. simpl in H1. contradiction.
destruct (delete_id i al) as [[??]|] eqn:?H.
specialize (IHal a0 l H3).
destruct IHal  as [? _]. specialize (H1 (eq_refl _)).
destruct H1.
subst.
split; intros.
inv H4.
split.
right; auto.
rewrite eqb_ident_false by auto. simpl. auto.
destruct H4.
destruct H4. congruence. rewrite eqb_ident_false in H5 by auto. simpl in H5.
subst; auto.
f_equal. f_equal.
eapply list_norepet_In_In; eauto.
split; intros. inv H1.
destruct H1.
rewrite eqb_ident_false in H4 by auto; simpl in H4.
destruct H1. congruence.
destruct al'; inv H4.
specialize (IHal x (filter (negb oo eqb_ident i oo fst) al) H3).
destruct IHal as [_ ?]. spec H4.
split; auto. inv H4.
Qed.

Lemma delete_id_None:
  forall {A} i (al: list (ident * A)),
    delete_id i al = None <-> ~ In i (map fst al).
Proof.
induction al as [|[j?]]; simpl; intros.
split; intros. intro; auto. auto.
if_tac.
subst.
split; intros. inv H. contradiction H; auto.
destruct (delete_id i al) as [[??]|] eqn:?H.
destruct IHal; split; intro.
inv H3.
contradiction H3. right.
destruct (in_dec ident_eq i (map fst al)); auto.
apply H2 in n. inv n.
split; intros. intros [?|?]. congruence.
rewrite IHal in H1. contradiction.
auto.
Qed.


Inductive augment_funspecs_rel: 
  forall (fds: list (ident * Clight.fundef)) (G:funspecs) (G': funspecs), Prop :=
| AF_cons1:  forall i G f G1 G' fd fds',
    delete_id i G = Some (f,G1) ->
    augment_funspecs_rel fds' G1 G' ->
    augment_funspecs_rel ((i,fd)::fds') G ((i,f)::G')
| AF_cons0: forall i G G' fds' fd,
    ~In i (map fst G) ->
    augment_funspecs_rel fds' G G' ->
    augment_funspecs_rel ((i,fd)::fds') G ((i, vacuous_funspec fd)::G')
| AF_nil: augment_funspecs_rel nil nil nil.

Lemma augment_funspecs'_e:
 forall fds G G',
     augment_funspecs' fds G = Some G' ->
     augment_funspecs_rel fds G G'.
Proof.
 induction fds as [|[i?]]; simpl; intros.
 destruct G; inv H. constructor.
 destruct (delete_id i G) as [[??]|] eqn:?H.
 destruct (augment_funspecs' fds l) eqn:?H; inv H.
 eapply AF_cons1; try eassumption.
 eauto.
 destruct (augment_funspecs' fds G) eqn:?H; inv H.
 eapply AF_cons0; try eassumption.
 intro.
 clear - H0 H.
 induction G as [|[j?]]; simpl in *; auto.
 if_tac in H0. inv H0.
 destruct H. congruence.
 destruct (delete_id i G); inv H0. destruct p. inv H3.
  auto.
 auto.
Qed.

Lemma augment_funspecs'_exists:
 forall G (builtins : list (ident * QP.builtin)) (fs : list (ident * fundef function))
  (B_LNR : list_norepet (map fst builtins))
  (H0 : list_norepet (map fst fs))
  (H2 : list_disjoint (map fst builtins) (map fst fs))
  (DNB : forallb not_builtin' fs = true)
  (G_LNR : list_norepet (map fst G))
  (Gsub: forall i, In i (map fst G) -> In i (map fst fs)),
 exists G' : funspecs,
  augment_funspecs'  (prog_funct' (map of_builtin builtins) ++  fs) G =
    Some G'.
Proof.
intros.
revert G G_LNR Gsub; induction builtins as [|[i?]]; [ simpl; induction fs as [|[i?]] | ]; intros.
-
 simpl.
 destruct G; eauto.
 specialize (Gsub (fst p)).
 spec Gsub. left; auto. inv Gsub.
-
  clear H2. simpl in H0; inv H0. simpl in DNB. rewrite andb_true_iff in DNB; destruct DNB.
  spec IHfs. auto.
  spec IHfs. intros ? ? ? ? ?. inv H1.
  spec IHfs. auto.
  simpl.
  destruct (delete_id i G) as [[fi G1]|] eqn:?H.
 +
  destruct (IHfs G1); auto; clear IHfs.
  apply delete_id_Some in H1. destruct H1 as [_ ?]. subst G1.
  apply list_norepet_map_fst_filter; auto. auto.
  apply delete_id_Some in H1. destruct H1. subst G1. 
  intros.
  apply list_in_map_inv in H4. destruct H4 as [[j ?] [? ?]]. simpl in H4; subst i0.
  rewrite filter_In in H5; destruct H5.
  simpl in H5.
  pose proof (eqb_ident_spec i j).
  destruct (eqb_ident i j); inv H5.
  assert (i <> j) by (clear - H6; intuition). clear H6.
  apply (in_map fst) in H4. specialize (Gsub _ H4). simpl in Gsub; destruct Gsub; auto.
  contradiction.
  auto.
  rewrite H4. eauto.
 +
  destruct (IHfs G); auto.
  intros.
  destruct (ident_eq i0 i). subst.
  elimtype False. clear - H1 H4. apply delete_id_None in H1. contradiction.
  apply Gsub in H4. destruct H4; auto. simpl in H4. congruence.
  rename x into G1.
  rewrite H4.
  eauto.
-
  simpl in H2.
  apply list_disjoint_consD in H2. destruct H2.
  simpl in B_LNR; inv B_LNR.
  spec IHbuiltins; auto.
  spec IHbuiltins; auto.
  destruct (IHbuiltins G) as [G1 ?]; auto; clear IHbuiltins.
  simpl. destruct b.
  simpl.
  assert (delete_id i G = None). {
   apply delete_id_None. contradict H; auto.
  }
  rewrite H3.
  rewrite H2. eauto.
Qed.

Lemma prog_funct_QP_prog_funct:
  forall prog p OK J1,
    prog = wholeprog_of_QPprog p OK J1 ->
    prog_funct prog = prog_funct' (map of_builtin (QP.prog_builtins p)) ++ @QPprog_funct function p. 
Proof.
  intros. subst. 
  unfold QPprog_funct, prog_funct.
  simpl.
  replace  (@QPprog_funct' function) with (@prog_funct' (fundef function) type)
       by (extensionality dl; induction dl as [|[i[|]]]; simpl; f_equal; auto).
  rewrite prog_funct'_app. auto.
Qed.

Lemma augment_funspecs_find_id_Some:
  forall fds G G',
  augment_funspecs_rel fds G G' ->
  list_norepet (map fst G) ->
  forall j f,  find_id j G = Some f -> find_id j G' = Some f.
Proof.
intros.
induction H. apply delete_id_Some in H; auto. destruct H.
simpl. if_tac. subst. apply find_id_i in H; auto. congruence.
subst. apply IHaugment_funspecs_rel.
apply list_norepet_map_fst_filter; auto.
rewrite find_id_filter_char by auto. rewrite H1. simpl.
rewrite eqb_ident_false by auto; auto.
simpl. rewrite if_false. auto.
intro; subst. apply H. apply find_id_e in H1. apply (in_map fst) in H1; auto.
auto.
Qed.

Lemma QPprog_funct'_filter_isGfun: 
  forall dl, QPprog_funct' (filter isGfun dl) = QPprog_funct' dl.
Proof.
 induction dl as [|[i[|]]]; simpl; auto; f_equal; auto.
Qed.

Lemma map_fst_prog_funct'_map_of_builtin:
  forall {F} dl, map fst (prog_funct' (map (@of_builtin F) dl)) = map fst dl.
Proof.
  induction dl as [|[i[]]]; simpl; auto; f_equal; auto.
Qed.

Lemma map_fst_map_of_builtin:
 forall {F} dl, map fst (map (@of_builtin F) dl) = map fst dl.
Proof.
 induction dl as [|[i[]]]; simpl; auto; f_equal; auto.
Qed.

Definition unspecified_info (ge: Genv.t (fundef function) type)
    (ix: ident * fundef function) :=
 let (id, g) := ix in
        match g with
        | Internal f => True
       | External ef argsig retsig cc =>  
          exists b, 
          Genv.find_symbol ge id = Some b /\
          Genv.find_funct_ptr ge b = Some g /\
          ef_sig ef =   {|
             sig_args := typlist_of_typelist argsig;
             sig_res := rettype_of_type retsig;
             sig_cc := cc_of_fundef (External ef argsig retsig cc) |}
 end. 

Lemma SF_semax_func:
  forall (Espec : OracleKind)
     (V: varspecs)
     (cs : compspecs)
     (ge: Genv.t (fundef function) type)
     (i : ident)
    (fd : Clight.fundef)
    (fds' : list (ident * Clight.fundef))
    (f : funspec)
     (G' G0 : funspecs)
    (H5 : ~ In i (map fst fds'))
    (H7 : @SF Espec cs V ge G0 i fd f)
    (H8 : @semax_func Espec V G0 cs ge fds' G'),
  @semax_func Espec V G0 cs ge ((i, fd) :: fds') ((i, f) :: G').
Proof.
intros.
 destruct fd.
  *
   destruct H7 as [? [? [? [? [? ?]]]]].
   destruct f.
   rewrite andb_true_iff in H; destruct H.
   destruct H4 as [b [? ?]].
   eapply semax_func_cons; try eassumption.
   rewrite H.
   rewrite id_in_list_false_i; auto.
  *
   destruct f, t1.
   hnf in H7; decompose [and] H7; clear H7.
   subst t0 c0 l.
   destruct H10 as [b [? ?]].  
   apply semax_func_cons_ext with b; auto.
   apply id_in_list_false_i; auto.
Qed.

Definition of_builtin' (ix: ident * QP.builtin) :=
  let (i,b) := ix in
  match b with QP.mk_builtin ef params ty cc => (i, @External function ef params ty cc) end.


Definition builtin_unspecified_OK (ge : Genv.t (fundef function) type)
   (ib: ident * QP.builtin) :=
 let (i,builtin) := ib in
  match Genv.find_symbol ge i with None => false
  | Some loc => 
    match Genv.find_funct_ptr ge loc with None => false
    | Some g => 
      andb (fundef_eq (snd (of_builtin' ib)) g)
      match g with
     | Internal _ => true
     | External ef argsig retsig cc =>  
            eqb_signature (ef_sig ef) 
              {|
             sig_args := typlist_of_typelist argsig;
             sig_res := rettype_of_type retsig;
             sig_cc := cc |}
      end
   end
  end.

Definition funct_unspecified_OK (ge : Genv.t (fundef function) type)
   (ib: ident * fundef function) :=
 let (i,g) := ib in
        match g with
     | Internal _ => true
     | External ef argsig retsig cc =>  
     match Genv.find_symbol ge i with None => false
     | Some b => 
       match Genv.find_funct_ptr ge b with None => false
        | Some g' => 
           andb (fundef_eq g g')
            (eqb_signature (ef_sig ef) 
              {|
             sig_args := typlist_of_typelist argsig;
             sig_res := rettype_of_type retsig;
             sig_cc := cc |})
      end
   end
  end.

Definition all_unspecified_OK (p: QP.program function) :=
   andb (forallb (builtin_unspecified_OK (QPglobalenv p)) (QP.prog_builtins p))
          (forallb (funct_unspecified_OK (QPglobalenv p)) (QPprog_funct p)) = true.

Lemma all_unspecified_OK_e:
   forall p,     
   all_unspecified_OK p ->
   forall i fd, In (i,fd) (map of_builtin' (QP.prog_builtins p) ++ QPprog_funct p) ->
      unspecified_info (QPglobalenv p) (i, fd).
Proof.
intros.
red in H. rewrite andb_true_iff in H.
destruct H.
rewrite in_app in H0.
destruct H0.
-
clear - H H0.
rewrite forallb_forall in H.
apply list_in_map_inv in H0.
destruct H0 as [[j []][? ?]].
simpl in H0.
symmetry in H0; inv H0.
apply H in H1.
unfold builtin_unspecified_OK in H1.
destruct (Genv.find_symbol (QPglobalenv p) i) eqn:?H; inv H1.
destruct (Genv.find_funct_ptr (QPglobalenv p) b) eqn:?H; inv H3.
rewrite andb_true_iff in H4. destruct H4.
destruct f; try discriminate.
rewrite !andb_true_iff in H2.
decompose [and] H2; clear H2.
apply eqb_calling_convention_prop in H5.
apply eqb_type_true in H7.
apply eqb_external_function_prop in H4.
apply eqb_typelist_prop in H8.
subst; auto.
exists b. split3; auto.
apply eqb_signature_prop in H3. auto.
-
clear H.
rewrite forallb_forall in H1.
apply H1 in H0. clear H1.
unfold funct_unspecified_OK in H0.
red.
destruct fd; auto.
destruct (Genv.find_symbol (QPglobalenv p) i) eqn:?H; inv H0.
destruct (Genv.find_funct_ptr (QPglobalenv p) b) eqn:?H; inv H2.
rewrite andb_true_iff in H3. destruct H3.
destruct f; try discriminate.
rewrite !andb_true_iff in H1.
decompose [and] H1; clear H1.
apply eqb_calling_convention_prop in H4.
apply eqb_type_true in H6.
apply eqb_external_function_prop in H3.
apply eqb_typelist_prop in H7.
subst.
apply eqb_signature_prop in H2.
exists b; split3; auto.
Qed.

Lemma augment_funspecs_semax_func:
forall (Espec : OracleKind)
  (G : funspecs)
  (V : varspecs)
  (fds : list (ident * fundef function))
  (ge : Genv.t (fundef function) type)
  (EXT_OK : forall (i : ident) (fd : fundef function),
               In (i, fd) fds -> unspecified_info ge (i, fd))
  (GFF : forall (i : ident) (fd : fundef function),
          find_id i fds = Some fd -> genv_find_func ge i fd)
  (cs : compspecs)
  (H : forall i phi, find_id i G = Some phi ->
         exists fd : fundef function, In (i, fd) fds /\ @SF Espec cs V ge G i fd phi)
  (V_FDS_LNR : list_norepet (map fst V ++ map fst fds))
  (VG_LNR : list_norepet (map fst V ++ map fst G))
  (G' : funspecs)
  (H3 : augment_funspecs_rel fds G G')
  (H20 : forall i fd, In (i, fd) fds -> isInternal (Gfun fd) = true -> In i (map fst G)),
  semax_func V G' ge fds G'.
Proof.
intros.
assert (HfdsG': map fst fds = map fst G'). {
  clear - H3. induction H3; simpl; f_equal; auto.
}
pose (G0 := G').
change G' with G0 at 1. 
assert (forall i phi, find_id i G' = Some phi ->
          exists fd, In (i,fd) fds /\ 
           (@SF Espec cs V ge G0 i fd phi
            \/ ~In i (map fst G) /\ 
                  ( unspecified_info ge (i,fd))
                    /\ phi = vacuous_funspec fd)). {
intros.
 assert (find_id i G = Some phi \/
      (exists fd, In (i,fd) fds /\  ~In i (map fst G) /\ 
           (@unspecified_info ge (i, fd)) /\ phi = vacuous_funspec fd)). {
  pose proof (list_norepet_append_right _ _ VG_LNR).
  clear - H3 H0 H1 EXT_OK.
  induction H3. 
  - apply delete_id_Some in H; auto.
     destruct H.
     simpl in H0. if_tac in H0. inv H0.
     apply find_id_i in H; auto.
     destruct (IHaugment_funspecs_rel); try clear IHaugment_funspecs_rel; 
       auto.
     intros; apply EXT_OK. right; auto.
    subst G1. apply list_norepet_map_fst_filter; auto.
    left. subst G1.
    apply find_id_filter_Some in H5; auto. destruct H5; auto.
   destruct H5 as [? [? [? ?]]]; right. exists x. split3; auto.
   right; auto. contradict H6; subst G1.
   clear - H6 H4. induction G as [|[j?]]; simpl in *; destruct H6; auto.
   subst. rewrite eqb_ident_false by auto. simpl; auto.
   destruct (eqb_ident i0 j) eqn:?H; simpl; auto.
 -
  simpl in H0. if_tac in H0. inv H0. right.
  exists fd; split3; auto. left; auto. split; auto.
  apply EXT_OK. left; auto.
  destruct IHaugment_funspecs_rel; eauto.
  intros; apply EXT_OK. right; auto.
  destruct H4 as [? [? ?]]; right; simpl; eauto.
 -  inv H0.
 } 
 destruct H1.
- apply H in H1.
 destruct H1 as [fd [? ?]]; exists fd; split; auto; left; auto.
 eapply SF_ctx_subsumption; try apply H2; auto.
 apply (list_norepet_append_right _ _ VG_LNR).
 apply cspecs_sub_refl.
 apply GFF; auto.
 apply find_id_i; auto. 
 rewrite list_norepet_app in V_FDS_LNR; apply V_FDS_LNR.
 {
 intro.
 pose proof (list_norepet_append_right _ _ VG_LNR).
 subst G0.
 assert (VG'_LNR: list_norepet (map fst V ++ map fst  G'))
     by (rewrite <- HfdsG'; auto).
 clear - H4 H3 VG_LNR VG'_LNR.
 destruct (find_id j V) eqn:?H.
 rewrite (semax_prog.make_context_g_mk_findV_mk _ _ VG_LNR j _ H).
 rewrite (semax_prog.make_context_g_mk_findV_mk _ _ VG'_LNR j _ H).
 apply sub_option_refl.
 destruct (find_id j G) eqn:?H.
 pose proof (augment_funspecs_find_id_Some _ _ _ H3 H4 _ _ H0).
 rewrite <- semax_prog.find_id_maketycontext_s in H0, H1.
 rewrite (semax_prog.make_tycontext_s_g V G j _ H0).
 rewrite (semax_prog.make_tycontext_s_g V _ j _ H1).
 apply sub_option_refl.
 rewrite semax_prog.make_tycontext_g_G_None by auto.
 rewrite H. simpl. auto.
 }
 {pose proof (list_norepet_append_right _ _ VG_LNR).
 subst G0. clear - H4 H3.
 intro.
 induction H3; try apply delete_id_Some in H; auto.
 destruct H. simpl. if_tac. subst. apply find_id_i in H; auto.
 rewrite H; apply subsumespec_refl.
 subst.
 rewrite find_id_filter_char in IHaugment_funspecs_rel; auto.
 destruct (find_id j G). simpl in IHaugment_funspecs_rel.
 rewrite eqb_ident_false in * by auto. apply IHaugment_funspecs_rel.
 apply list_norepet_map_fst_filter; auto.
 simpl. auto.
 simpl. if_tac. subst. apply find_id_None_iff in H. rewrite H. simpl; auto.
 apply IHaugment_funspecs_rel; auto.
 simpl; auto.
 }
- 
 destruct H1 as [? [? ?]]; eauto.
}
clearbody G0.
assert (H0': forall (i : ident) (phi : funspec),
     find_id i G' = Some phi ->
     exists fd : fundef function,
       In (i, fd) fds /\
       (@SF Espec cs V ge G0 i fd phi \/
        ~ In i (map fst G) /\
        (isInternal (Gfun fd) = false /\ unspecified_info ge (i, fd))
        /\  phi = vacuous_funspec fd)). {
   clear - H0 H20.
   intros. destruct (H0 _ _ H); clear H0.
   exists x. destruct H1; split; auto. destruct H1; [left|right]; auto.
  destruct H1 as [? [? ?]]; split3; auto. split; auto.
  destruct (isInternal (Gfun x)) eqn:?H; auto.
  apply (H20 _ _ H0) in H4. contradiction.
}
clear H0; rename H0' into H0.
pose proof (list_norepet_append_right _ _ VG_LNR).
clear - H3 H0 H1 V_FDS_LNR HfdsG' .
induction H3; [ | | apply semax_func_nil]; rename IHaugment_funspecs_rel into IH.
-
 rewrite list_norepet_app in V_FDS_LNR.
 destruct V_FDS_LNR as [V_LNR [ FDS_LNR DISJ ]].
 simpl in FDS_LNR; inv FDS_LNR.
 rewrite delete_id_Some in H; auto. destruct H.
 destruct (H0 i f). simpl. rewrite if_true by auto. auto.
 destruct H4 as [? [? | ?]]. simpl in H4.
 destruct H4; [ | apply (in_map fst) in H4; simpl in H4; contradiction].
 symmetry in H4; inv H4.
 spec IH. {
   rewrite list_norepet_app; split3; auto.
   apply list_disjoint_cons_right in DISJ; auto.
 }
 simpl in HfdsG'; inv HfdsG'.
 specialize (IH H4).
 spec IH. {
   intros.
   assert (i0<>i). {intro; subst i0. rewrite H4 in H5. apply H5.
      apply find_id_In_map_fst in H2; auto.
   }
   destruct (H0 i0 phi); clear H0.
   simpl. rewrite if_false by auto. auto.
   destruct H9 as [? [ ? | [H99 [? ?]]]].
   simpl in H0. destruct H0; [congruence | ].
   exists x; auto.
   exists x; split.  simpl in H0. destruct H0; auto; congruence. right; split3; auto.
   contradict H99. apply In_map_fst_filter3 in H99; auto.
  }
  spec IH.   apply list_norepet_map_fst_filter; auto.
  eapply SF_semax_func; eauto.
 *
   subst.
   simpl in HfdsG'; inv HfdsG'.
   destruct H7.
   apply (in_map fst) in H. simpl in H; contradiction.
-
   simpl in HfdsG'; inv HfdsG'.
   spec IH. {
     rewrite list_norepet_app in V_FDS_LNR; destruct V_FDS_LNR as [? [??]].
     simpl in H5. inv H5.
     rewrite list_norepet_app; split3; auto.
     apply list_disjoint_cons_right in H6; auto.   
   }
   specialize (IH H4).
   spec IH. {
       intros.
       assert (i0<>i). {intro; subst i0.
       rewrite list_norepet_app in V_FDS_LNR; destruct V_FDS_LNR as [_ [? _]].
      simpl in H5; inv H5.
      apply H8. rewrite H4.   
      apply find_id_In_map_fst in H2; auto.
      }
     destruct (H0 i0 phi); clear H0.
     simpl. rewrite if_false by auto. auto.
      destruct H6 as [? [? | [H99 [? ?]]]].
     simpl in H0. destruct H0; [congruence | ].
     exists x; auto.
     exists x; split; auto.  simpl in H0.  destruct H0; [congruence|].  auto.
  }
   specialize (IH H1).
   edestruct (H0 i) as [fd' ?]. simpl. rewrite if_true by auto. reflexivity.
   destruct H2 as [? [?|[? [? ?]]]].
 +
   simpl in H2. destruct H2. symmetry in H2; inv H2.
   2:{ apply (in_map fst) in H2. simpl in H2.
      rewrite list_norepet_app in V_FDS_LNR; destruct V_FDS_LNR as [_ [? _]].
      simpl in H6; inv H6. contradiction.
   }
   clear H0.
   eapply SF_semax_func; eauto.
      rewrite list_norepet_app in V_FDS_LNR; destruct V_FDS_LNR as [_ [? _]].
      simpl in H0; inv H0. auto.
  +
   simpl in H2. destruct H2. symmetry in H2; inv H2.
   2:{ apply (in_map fst) in H2. simpl in H2.
      rewrite list_norepet_app in V_FDS_LNR; destruct V_FDS_LNR as [_ [? _]].
      simpl in H8; inv H8. contradiction.
   }
   destruct H6 as [H99 H6].
   destruct fd.
   inv H99.
   destruct H6 as [b [? [? ?]]].
   eapply semax_func_cons_ext_vacuous; try eassumption. 
   rewrite list_norepet_app in V_FDS_LNR; destruct V_FDS_LNR as [_ [? _]].
   destruct H6.
   inv H9. apply id_in_list_false_i; auto.
Qed.

Definition prog_of_component {Espec Externs p Exports GP G}
  (c: @Component Espec (QPvarspecs p) Externs nil p Exports GP G)
  (H: cenv_built_correctly
         (map compdef_of_compenv_element
            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p)
            (projT1 (proj2 (Comp_prog_OK c))))  =  Errors.OK tt)  :=
   wholeprog_of_QPprog p (Comp_prog_OK c) 
   (cenv_built_correctly_e _ _ H).

Lemma WholeComponent_semax_func:
 forall {Espec Externs p Exports GP G}
  (c: @Component Espec (QPvarspecs p) Externs nil p Exports GP G)
  (EXT_OK: all_unspecified_OK p)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)
  (CBC: cenv_built_correctly
         (map compdef_of_compenv_element
            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p)
            (projT1 (proj2 (Comp_prog_OK c))))  =  Errors.OK tt),  (* should be part of QPprogram_OK *)
 let prog := prog_of_component c CBC in
  @semax_func Espec
  (QPvarspecs p) (augment_funspecs prog G) (Comp_cs c)
  (Genv.globalenv prog)
  (SeparationLogic.prog_funct prog)
  (augment_funspecs prog G).
Proof.
intros.
assert (H := all_unspecified_OK_e _ EXT_OK).
clear EXT_OK. rename H into EXT_OK. 
unfold QPprog_funct in EXT_OK.
replace (map of_builtin' (QP.prog_builtins p))
with (@QPprog_funct' function (map of_builtin (QP.prog_builtins p))) in EXT_OK
  by (clear; induction (QP.prog_builtins p) as [|[i[]]]; simpl; auto; f_equal; auto).
assert (GFF: forall i fd, 
              find_id i (prog_funct' (map of_builtin (QP.prog_builtins p)) ++ QPprog_funct p) = Some fd ->
                               genv_find_func (Genv.globalenv prog) i fd). {
 intros.
  rewrite <-  (prog_funct_QP_prog_funct _ p (Comp_prog_OK c) 
       (cenv_built_correctly_e _ _ CBC)) in H by reflexivity.
  fold prog in H.
  apply find_id_e in H. 
 apply semax_prog.find_funct_ptr_exists.
 subst prog; unfold prog_defs_names; simpl.
 rewrite map_app.
 rewrite map_fst_map_of_builtin.
 apply (proj1 (Comp_prog_OK c)).
 apply (semax_prog.in_prog_funct_in_prog_defs _ _ _ H).
}  
unfold augment_funspecs.
change SeparationLogic.prog_funct with prog_funct in *.
change (Genv.globalenv prog) with (QPglobalenv p) in *.
rewrite (prog_funct_QP_prog_funct _ p (Comp_prog_OK c) 
   (cenv_built_correctly_e _ _ CBC)) by reflexivity.
clear prog CBC.
assert (B_LNR: list_norepet (map fst (QP.prog_builtins p))). {
 destruct (Comp_prog_OK c) as [? _].
 rewrite list_norepet_app in H; destruct H; auto.
}
unfold QPprog_funct.
assert  (Gsub: forall i, In i (map fst G) -> 
             In i (map fst (QPprog_funct' (PTree.elements (QP.prog_defs p))))). {
  intros.
  rewrite <- (Comp_G_dom c i) in H.
  rewrite in_app in H; destruct H.
  apply IntIDs_elim in H. destruct H as [f ?].
  clear - H. induction (PTree.elements _) as [|[j?]]. inv H. destruct H. inv H. left; auto. destruct g;  simpl. right; auto. auto.
     apply (Comp_Externs c i) in H. destruct H as [? [? [? [? ?]]]].
  clear - H. apply PTree.elements_correct in H.
  induction (PTree.elements _) as [|[j?]]. inv H. destruct H. inv H. left; auto. destruct g;  simpl. right; auto. auto.
}
assert (forall i phi, 
    find_id i G = Some phi ->
   exists fd, In (i, fd) (prog_funct' (map of_builtin (QP.prog_builtins p)) ++ QPprog_funct' (PTree.elements (QP.prog_defs p))) /\
 @SF Espec (Comp_cs c) (QPvarspecs p)
           (QPglobalenv p) G i fd phi). {
  intros.
  specialize (Gsub _ (find_id_In_map_fst _ _ _ H)).
  apply list_in_map_inv in Gsub. destruct Gsub as [[j f] [? ?]]. simpl in H0; subst j.
  exists f; split; auto.
  rewrite in_app; right; auto.
  apply  (Comp_G_justified c); auto.
  clear - H1.
  apply PTree.elements_complete.
  induction (PTree.elements (QP.prog_defs p)). inv H1.
  destruct a. destruct g; simpl in *; auto.
  destruct H1; [left | right]; simpl in *. inv H; auto. auto.
 }
assert (list_norepet (map fst (QPprog_funct' (PTree.elements (QP.prog_defs p))))). {
   clear.
   pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
   induction (PTree.elements (QP.prog_defs p)) as [|[i[?|?]]]; simpl in *; auto.
  inv H. constructor; auto.
  contradict H2. clear - H2. induction l as [|[j[|]]]; simpl in *; auto.
    destruct H2; auto; right. inv H; auto.
}
rewrite <- QPprog_funct'_filter_isGfun in Gsub,H,H0|-*.
assert (forallb isGfun (filter isGfun (PTree.elements (QP.prog_defs p))) = true)
  by (clear; induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto).
assert (list_disjoint  (map fst (QP.prog_builtins p))
             (map fst (filter isGfun (PTree.elements (QP.prog_defs p))))). {
 clear - c.
 destruct (Comp_prog_OK c) as [? _].
 rewrite list_norepet_app in H; destruct H as [_ [_ ?]].
 intros i j ? ? ?; apply (H i j); auto.
 apply In_map_fst_filter3 in H1; auto.
}
assert (DNB: forallb not_builtin (filter isGfun (PTree.elements (QP.prog_defs p))) = true). {
    clear - DEFS_NOT_BUILTIN.
    induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto.
    rewrite andb_true_iff in DEFS_NOT_BUILTIN; destruct DEFS_NOT_BUILTIN.
    rewrite andb_true_iff; split; auto.
}
assert (G_LNR := Comp_G_LNR c).
clear DEFS_NOT_BUILTIN.
assert (V_FDS_LNR: list_norepet
          (map fst (QPvarspecs p) ++ 
             (map fst (prog_funct' (map of_builtin (QP.prog_builtins p)) ++
                            QPprog_funct' (filter isGfun (PTree.elements (QP.prog_defs p))))))). {
 pose proof (proj1 (Comp_prog_OK c)).
 clear - H3.
 rewrite map_app.
 rewrite list_norepet_app in H3.
 destruct H3 as [? [? ?]].
 rewrite !list_norepet_app.
 rewrite map_fst_prog_funct'_map_of_builtin.
 replace (map fst (QPprog_funct' (filter isGfun (PTree.elements (QP.prog_defs p)))))
    with (map fst (filter isGfun (PTree.elements (QP.prog_defs p))))
  by ( clear; induction (PTree.elements (QP.prog_defs p)) as [|[?[|]]]; simpl; auto; f_equal; auto).
 split3; [ | split3 | ]; auto.
 apply QPvarspecs_norepet.
 apply list_norepet_map_fst_filter; auto.
 eapply list_disjoint_mono; try apply H1; auto.
 intros.
 apply In_map_fst_filter3 in H2; auto.
 apply list_disjoint_app_R.
 apply list_disjoint_sym.
 eapply list_disjoint_mono; try apply H1; auto.
 intros. unfold QPvarspecs, QPprog_vars in H2.
 clear - H2; induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto.
 destruct H2; auto.
 clear. unfold QPvarspecs, QPprog_vars.
 intros i j ? ? ?; subst j.
 apply list_in_map_inv in H; destruct H as [[??][??]]. simpl in *; subst i0.
 apply list_in_map_inv in H0; destruct H0 as [[??][??]]. simpl in *; subst i0.
 apply filter_In in H0. destruct H0.
 destruct g; inv H0.
 pose proof (PTree.elements_keys_norepet (QP.prog_defs p)).
 induction (PTree.elements (QP.prog_defs p)) as [|[j?]]. inv H.
 simpl  in H. destruct H. inv H.
 inv H0. simpl in H1.
 apply H3. clear - H1. induction l as [|[j[|]]]; simpl in *; auto. destruct H1. inv H; auto. right; auto.
 inv H0.
 assert (i<>j). intro; subst j. apply H4. apply (in_map fst) in H; auto.
 destruct g; simpl in H1; auto.
 destruct H1; auto. inv H1; auto.
}
destruct (augment_funspecs'_exists G (QP.prog_builtins p) (QPprog_funct' (filter isGfun (PTree.elements (QP.prog_defs p)))))  as [G' ?]; auto.
 forget (filter isGfun (PTree.elements (QP.prog_defs p))) as fs.
 clear - H2. intros i j ? ? ?. apply (H2 i j); auto. clear - H0.
   induction fs as [|[i[|]]]; simpl in *; auto. destruct H0;[left|right]; auto.
 forget (filter isGfun (PTree.elements (QP.prog_defs p))) as fs.
 clear - DNB.
   induction fs as [|[i[|]]]; simpl in *; auto.
  rewrite andb_true_iff in *|-*. destruct DNB; split; auto.
 rewrite H3.
apply augment_funspecs'_e in H3.
unfold QPprog_funct in GFF.
rewrite <- QPprog_funct'_filter_isGfun in GFF.
rewrite <- (QPprog_funct'_filter_isGfun (PTree.elements _))  in EXT_OK.

assert (H20: forall i fd, In (i,fd) (prog_funct' (map of_builtin (QP.prog_builtins p)) ++
                                 QPprog_funct' (filter isGfun (PTree.elements (QP.prog_defs p)))) ->
                                  isInternal (Gfun fd)=true -> In i (map fst G)). {
  intro i. pose proof (Comp_G_dom c i).
  clear - H4.
  intros.
  rewrite in_app in H. destruct H.
  induction (QP.prog_builtins p) as [|[j[]]]. inv H.
  simpl in H; destruct H. inv H. inv H0.
  auto.
  rewrite <- H4. rewrite in_app; left.
  destruct fd; inv H0.
  apply @IntIDs_i with (f:=f).
  apply PTree.elements_complete. 
  induction (PTree.elements (QP.prog_defs p)) as [|[j[|]]]. inv H.
  destruct H. inv H; simpl; auto.
  right; auto. right; auto.
}

assert (VG_LNR: list_norepet (map fst (QPvarspecs p) ++ map fst  G)). {
  pose proof (Comp_LNR c). rewrite <- app_nil_end in H4.
  auto.
}
forget (filter isGfun (PTree.elements (QP.prog_defs p))) as fs.
forget (QP.prog_builtins p) as builtins.
replace (@QPprog_funct' function) with (@prog_funct' (fundef function) type) in *
  by (clear; extensionality al; induction al as [|[i[|]]]; simpl; auto; f_equal; auto).
forget (prog_funct' (map of_builtin builtins) ++ prog_funct' fs) as fds.
forget (QPvarspecs p) as V.
forget (QPglobalenv p) as ge.
forget (Comp_cs c) as cs.
clear - H H3 V_FDS_LNR VG_LNR GFF EXT_OK H20.
eapply augment_funspecs_semax_func; eassumption.
Qed.

Definition WholeProgSafeType  {Espec E p Exports GP mainspec}
       (c: exists G, 
             find_id (QP.prog_main p) G = None /\
             @Component Espec (QPvarspecs p) E nil p Exports GP 
         (G_merge
                 [(QP.prog_main p, mainspec)] G))
             (z: @OK_ty Espec) :=
 exists cs, exists OK, exists CBC, exists G, 
@semax_prog Espec cs
   (wholeprog_of_QPprog p OK
    (cenv_built_correctly_e
         (map compdef_of_compenv_element
            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 OK)))
         CBC))
    z (QPvarspecs p) 
      (G_merge [(QP.prog_main p, mainspec)] G).

Lemma WholeComponent_semax_prog:
 forall {Espec Externs p Exports GP mainspec}
  (c: exists G, 
    find_id (QP.prog_main p) G = None /\
     @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: exists post, mainspec = QPmain_spec_ext' p z post)
  (MAIN': isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)))
  (EXT_OK: all_unspecified_OK p)
  (ALIGNED: QPall_initializers_aligned p = true) (* should be part of QPprogram_OK *)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)  (* should be part of QPprogram_OK *)
  (CBC: forall H,
    cenv_built_correctly
        (map compdef_of_compenv_element
           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) 
           = Errors.OK tt),
  WholeProgSafeType c z.
Proof.
 intros ? ? ? ? ? mainspec; intros.
 destruct c as [G [NO_MAIN c]].
 pose (prog := prog_of_component c (CBC _)).
 red.
 exists (Comp_cs c).
 exists (Comp_prog_OK c).
 exists (CBC _).
 exists G.
 split3; [ | | split3; [ | | split]].
 4: change SeparationLogicAsLogicSoundness.MainTheorem.CSHL_MinimumLogic.CSHL_Def.semax_func
  with semax_func.
-
 subst prog; simpl.
 unfold prog_defs_names. simpl.
 apply compute_list_norepet_i.
 clear - c.
 rewrite map_app.
 destruct (Comp_prog_OK c).
 rewrite map_map. 
 replace (fun x : ident * QP.builtin => fst (of_builtin x)) with (@fst ident QP.builtin); auto.
 extensionality x. destruct x,b; simpl; auto.
-
 red. unfold SeparationLogic.prog_vars;
 subst prog; simpl.
 clear - ALIGNED.
 unfold QPall_initializers_aligned in *.
 unfold QPprog_vars in ALIGNED.
  replace  (SeparationLogic.prog_vars'
     (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)))
    with  (SeparationLogic.prog_vars'(PTree.elements (QP.prog_defs p)))
       by (induction (QP.prog_builtins p) as [|[i ?]]; try destruct b; simpl; auto).
 induction (PTree.elements (QP.prog_defs p)) as [|[i?]]; auto.
 destruct g; auto.
 simpl in ALIGNED|-*.
 rewrite andb_true_iff in ALIGNED|-*; destruct ALIGNED; auto.
-
  f_equal.
  apply (proj1 (QPcompspecs_OK_e _ (proj2 (Comp_prog_OK c)))).
-
 apply (@WholeComponent_semax_func _ _ _ _ _ _ c EXT_OK DEFS_NOT_BUILTIN).
-
  subst prog; simpl.
  unfold QPvarspecs, QPprog_vars, SeparationLogic.prog_vars. simpl.
  clear.
  replace  (SeparationLogic.prog_vars'
     (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)))
    with  (SeparationLogic.prog_vars'(PTree.elements (QP.prog_defs p)))
       by (induction (QP.prog_builtins p) as [|[i ?]]; try destruct b; simpl; auto).
  induction (PTree.elements (QP.prog_defs p)) as [|[i?]].
  simpl. auto.
  simpl. destruct g; auto.
  simpl.
  rewrite eqb_ident_true by auto.
  rewrite eqb_type_refl by auto.
  simpl; auto.
- simpl find_id.
   unfold augment_funspecs.
   change SeparationLogic.prog_funct with prog_funct.
   erewrite prog_funct_QP_prog_funct; [ | reflexivity].
  set (G1 := G_merge [(QP.prog_main p, mainspec)] G).
   destruct (augment_funspecs'_exists G1 (QP.prog_builtins p) (QPprog_funct p)) 
     as [G' ?]; auto.
   * 
   apply (list_norepet_append_left _ _ (proj1 (Comp_prog_OK c))).
   *
   pose proof (list_norepet_append_right _ _ (proj1 (Comp_prog_OK c))).
   unfold QPprog_funct.
   clear - H. forget (PTree.elements (QP.prog_defs p)) as al.
   induction al as [|[i[|]]]; simpl in *; auto. inv H; constructor; auto.
   contradict H2. clear - H2; induction al as [|[j[|]]]; simpl in *; auto. destruct H2; auto.
   inv H; auto.
   *
   assert (H1 := proj1 (Comp_prog_OK c)).
   rewrite list_norepet_app in H1; destruct H1 as [_ [_ H1]].
   eapply assoclists.list_disjoint_mono; try apply H1; auto.
   clear; intros. unfold QPprog_funct in H.
   induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto. destruct H; auto.
   *
   clear - DEFS_NOT_BUILTIN.
   unfold QPprog_funct. induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto.
   rewrite andb_true_iff in *|-*. tauto.
   *
     apply (Comp_G_LNR c).
   *
   intros.
   fold G1 in c.
   rewrite <- (Comp_G_dom c) in H.
   rewrite in_app in H; destruct H.
   apply IntIDs_elim in H; destruct H.
   unfold QPprog_funct.
   clear - H. induction (PTree.elements (QP.prog_defs p)) as [|[j[|]]]; simpl in *; auto.
   destruct H; auto. inv H; auto.   destruct H; auto. inv H; auto.
   apply (Comp_Externs c i) in H.
   destruct H as [? [? [? [? ?]]]].
   apply PTree.elements_correct in H.
   unfold QPprog_funct.
   clear - H. induction (PTree.elements (QP.prog_defs p)) as [|[j[|]]]; simpl in *; auto.
   destruct H; auto. inv H; auto.   destruct H; auto. inv H; auto.
   *
   change (G_merge _ _) with G1.
   rewrite H.
   apply augment_funspecs'_e in H.
   destruct MAIN as [post MAIN].
   change (prog_main prog) with (QP.prog_main p).
   assert   (MAINx: find_id (QP.prog_main p) G1 = Some (QPmain_spec_ext' p z post)). {
     apply G_merge_find_id_SomeNone.
     simpl. rewrite if_true by auto. f_equal; auto. auto.
   }
   rewrite (augment_funspecs_find_id_Some _ _ _ H (Comp_G_LNR c) _ _ MAINx).
   exists post.
   unfold QPmain_spec_ext', main_spec_ext'.
   f_equal.
   subst prog. unfold main_pre, SeparationLogic.main_pre.
   unfold SeparationLogic.prog_vars. simpl.
   unfold QPprog_vars.
   replace  (SeparationLogic.prog_vars'
     (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)))
    with  (SeparationLogic.prog_vars'(PTree.elements (QP.prog_defs p)))
       by (clear; induction (QP.prog_builtins p) as [|[i ?]]; try destruct b; simpl; auto).
   extensionality gv rho.
   normalize. f_equal. f_equal. f_equal. f_equal.
  clear.
  induction (PTree.elements (QP.prog_defs p)) as [|[i?]]; auto.
  simpl.
  destruct g; auto.
  f_equal; auto.
Qed.

Ltac QPlink_prog_tac p1 p2 :=
  let p' :=  uconstr:(QPlink_progs p1 p2) in
  let p'' := eval vm_compute in p' in
  lazymatch p'' with
  | Errors.OK ?p => uconstr:(@abbreviate _ p)
  | Errors.Error ?m => fail "QPlink_progs failed:" m
   end.

Ltac QPlink_prog_tac' := 
 match goal with |- QPlink_progs ?p1 ?p2 = Errors.OK ?p =>
   let p' := QPlink_prog_tac p1 p2 in unify p p'; reflexivity
 end.

Ltac proveWholeComponent := 
 match goal with |- @WholeCompType _ _ ?coreprog _ _ _ _ ?mainprog _ _ _ _ =>
   let p := QPlink_prog_tac mainprog coreprog in
    apply (@WholeComponent _ _ _ _ _ _ _ _ p)
  end;
 [ reflexivity
 | list_disjoint_tac || fail "Varspecs of core-VSU overlap with funspecs of main-Component"
 | FDM_tac 

 | list_disjoint_tac  || fail "Externs of main-Component overlap with internal funspecs of core-VSU"
 | list_disjoint_tac  || fail "Externs of core-VSU overlap with internal funspecs of main-Component"
 | reflexivity || fail "Linked program has nonempty Imports"
 | reflexivity ||
    fail "main is improperly found in the core- VSU Exports or internal IDs or Externs"
 ].

Ltac proveWholeProgSafe :=
apply WholeComponent_semax_prog;
 [ eexists; reflexivity || fail "precondition of main is not main_pre"
 | apply I  || fail "no function body found for main"
 | reflexivity || fail "one of the unspecified builtins or externals has the wrong signature, or there is an unspecified internal function"
 | reflexivity || fail "a global initializer is not aligned"
 | reflexivity || fail "Impossible: one of the QP.prog_defs is a builtin"
 | intro; reflexivity || fail "Surprising: cenv_built_correctly fails"].



Section binary_intersection'_funspec_sub_mono.

Definition sigBool_left {A B ts1} (x:functors.MixVariantFunctor._functor
               ((fix dtfr (T : rmaps.TypeTree) : functors.MixVariantFunctor.functor :=
                   match T with
                   | rmaps.ConstType A => functors.MixVariantFunctorGenerator.fconst A
                   | rmaps.Mpred => functors.MixVariantFunctorGenerator.fidentity
                   | rmaps.DependentType n => functors.MixVariantFunctorGenerator.fconst (@nth Type n ts1 unit)
                   | rmaps.ProdType T1 T2 => functors.MixVariantFunctorGenerator.fpair (dtfr T1) (dtfr T2)
                   | rmaps.ArrowType T1 T2 => functors.MixVariantFunctorGenerator.ffunc (dtfr T1) (dtfr T2)
                   | rmaps.SigType I0 f0 => @functors.MixVariantFunctorGenerator.fsig I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.PiType I0 f0 => @functors.MixVariantFunctorGenerator.fpi I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.ListType T0 => functors.MixVariantFunctorGenerator.flist (dtfr T0)
                   end) A) mpred):
{i : bool &
             functors.MixVariantFunctor._functor
               ((fix dtfr (T : rmaps.TypeTree) : functors.MixVariantFunctor.functor :=
                   match T with
                   | rmaps.ConstType A => functors.MixVariantFunctorGenerator.fconst A
                   | rmaps.Mpred => functors.MixVariantFunctorGenerator.fidentity
                   | rmaps.DependentType n => functors.MixVariantFunctorGenerator.fconst (@nth Type n ts1 unit)
                   | rmaps.ProdType T1 T2 => functors.MixVariantFunctorGenerator.fpair (dtfr T1) (dtfr T2)
                   | rmaps.ArrowType T1 T2 => functors.MixVariantFunctorGenerator.ffunc (dtfr T1) (dtfr T2)
                   | rmaps.SigType I0 f0 => @functors.MixVariantFunctorGenerator.fsig I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.PiType I0 f0 => @functors.MixVariantFunctorGenerator.fpi I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.ListType T0 => functors.MixVariantFunctorGenerator.flist (dtfr T0)
                   end) (if i then A else B)) mpred}.
Proof. exists true; trivial. Defined.
Definition sigBool_right {A B ts1} (x:functors.MixVariantFunctor._functor
               ((fix dtfr (T : rmaps.TypeTree) : functors.MixVariantFunctor.functor :=
                   match T with
                   | rmaps.ConstType A => functors.MixVariantFunctorGenerator.fconst A
                   | rmaps.Mpred => functors.MixVariantFunctorGenerator.fidentity
                   | rmaps.DependentType n => functors.MixVariantFunctorGenerator.fconst (@nth Type n ts1 unit)
                   | rmaps.ProdType T1 T2 => functors.MixVariantFunctorGenerator.fpair (dtfr T1) (dtfr T2)
                   | rmaps.ArrowType T1 T2 => functors.MixVariantFunctorGenerator.ffunc (dtfr T1) (dtfr T2)
                   | rmaps.SigType I0 f0 => @functors.MixVariantFunctorGenerator.fsig I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.PiType I0 f0 => @functors.MixVariantFunctorGenerator.fpi I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.ListType T0 => functors.MixVariantFunctorGenerator.flist (dtfr T0)
                   end) B) mpred):
{i : bool &
             functors.MixVariantFunctor._functor
               ((fix dtfr (T : rmaps.TypeTree) : functors.MixVariantFunctor.functor :=
                   match T with
                   | rmaps.ConstType A => functors.MixVariantFunctorGenerator.fconst A
                   | rmaps.Mpred => functors.MixVariantFunctorGenerator.fidentity
                   | rmaps.DependentType n => functors.MixVariantFunctorGenerator.fconst (@nth Type n ts1 unit)
                   | rmaps.ProdType T1 T2 => functors.MixVariantFunctorGenerator.fpair (dtfr T1) (dtfr T2)
                   | rmaps.ArrowType T1 T2 => functors.MixVariantFunctorGenerator.ffunc (dtfr T1) (dtfr T2)
                   | rmaps.SigType I0 f0 => @functors.MixVariantFunctorGenerator.fsig I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.PiType I0 f0 => @functors.MixVariantFunctorGenerator.fpi I0 (fun i0 : I0 => dtfr (f0 i0))
                   | rmaps.ListType T0 => functors.MixVariantFunctorGenerator.flist (dtfr T0)
                   end) (if i then A else B)) mpred}.
Proof. exists false; trivial. Defined.

Lemma binary_intersection'_funspec_sub_mono {f c A1 P1 Q1 P1ne Q1ne B1 R1 S1 R1ne S1ne phi1 psi1 Phi1 Psi1 
             A2 P2 Q2 P2ne Q2ne B2 R2 S2 R2ne S2ne phi2 psi2 Phi2 Psi2}
(Hphi: funspec_sub phi1 phi2)
(Hpsi: funspec_sub psi1 psi2):
funspec_sub (@binary_intersection' f c A1 P1 Q1 P1ne Q1ne B1 R1 S1 R1ne S1ne phi1 psi1 Phi1 Psi1)
            (@binary_intersection' f c A2 P2 Q2 P2ne Q2ne B2 R2 S2 R2ne S2ne phi2 psi2 Phi2 Psi2).
Proof.
split; [ split; trivial | intros].
subst.
unfold binarySUMArgs. destruct x2; simpl. destruct x.
+ clear Hpsi. destruct Hphi as [_ Hphi].
  eapply derives_trans. apply (Hphi ts2 _f gargs). clear Hphi.
  Intros ts1 x1 F. Exists ts1 (@sigBool_left A1 B1 ts1 x1) F; simpl.
  entailer.
+ clear Hphi. destruct Hpsi as [_ Hpsi].
  eapply derives_trans. apply (Hpsi ts2 _f gargs). clear Hpsi.
  Intros ts1 x1 F. Exists ts1 (@sigBool_right A1 B1 ts1 x1) F; simpl.
  entailer.
Qed.
End binary_intersection'_funspec_sub_mono.