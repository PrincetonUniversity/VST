From compcert.export Require Import Clightdefs.
From VST.veric Require Import base align_mem composite_compute compspecs.
Import compcert.lib.Maps.

Transparent Archi.ptr64.

(* from call_lemmas *)
Lemma Forall_ptree_elements_e:
  forall A (F: AST.ident * A -> Prop) m i v,
   Forall F (PTree.elements m) ->
   m ! i = Some v ->
   F (i,v).
Proof.
 intros.
 apply PTree.elements_correct in H0.
 induction (PTree.elements m).
 inv H0.
 inv H. inv H0; auto.
Qed.

(* copied from floyd/forward *)
(**** make_compspecs ****)

Lemma composite_env_consistent_i':
  forall (f: composite -> Prop) (env: composite_env),
   Forall (fun idco => f (snd idco)) (PTree.elements env) ->
   (forall id co, env ! id = Some co -> f co).
Proof.
intros.
pose proof (Forall_ptree_elements_e _ (fun idco : positive * composite => f (snd idco))).
simpl in H1.
eapply H1; eassumption.
Qed.

Lemma composite_env_consistent_i:
  forall (f: composite_env -> composite -> Prop) (env: composite_env),
   Forall (fun idco => f env (snd idco)) (PTree.elements env) ->
   (forall id co, env ! id = Some co -> f env co).
Proof.
intros.
eapply composite_env_consistent_i'; eassumption.
Qed.

Lemma legal_alignas_env_consistency': forall (cenv : composite_env) (ha_env : PTree.t Z) (la_env: PTree.t legal_alignas_obs),
  composite_env_consistent cenv ->
  la_env = legal_alignas_env cenv ha_env ->
  legal_alignas_env_consistent cenv ha_env la_env.
Proof.
  intros.
  subst.
  apply legal_alignas_env_consistency; auto.
Qed.

Lemma legal_alignas_env_completeness': forall (cenv : composite_env) (ha_env : PTree.t Z) (la_env: PTree.t legal_alignas_obs),
  la_env = legal_alignas_env cenv ha_env ->
  legal_alignas_env_complete cenv la_env.
Proof.
  intros.
  subst.
  apply legal_alignas_env_completeness; auto.
Qed.

Lemma Zgeb0_ge0: forall n, Z.geb n 0 = true -> (n >= 0)%Z.
Proof.
intros.
apply Z.geb_le in H. lia.
Qed.

Lemma prove_alignof_two_p (i: Z) : 
    i = two_power_nat (Nat.log2_up (Z.to_nat i)) ->
exists n: nat, i = two_power_nat n.
Proof.
intros. eexists; eassumption.
Qed.

Lemma prove_Zdivide (a b: Z): b = Z.mul (Z.div b a) a -> Z.divide a b.
Proof.
intros. eexists. eassumption.
Qed.

Ltac simplify_composite_of_def d :=
   let d := eval hnf in d in
  match d with
 Errors.OK 
   {|  co_su := ?su;
       co_members := ?m;
       co_attr := ?a;
       co_sizeof := ?sz;
       co_alignof := ?al;
       co_rank := ?rank;
       co_sizeof_pos := _;
       co_alignof_two_p := _;
       co_sizeof_alignof := _ |}  =>
  let sz := eval compute in sz in 
  let al := eval compute in al in 
  let rank := eval compute in rank in 
  let sp := constr:(Zgeb0_ge0 sz (eq_refl _)) in 
  let altwo := constr:(prove_alignof_two_p al (eq_refl _)) in
  let sa := constr:(prove_Zdivide al sz (eq_refl _)) in
   let d := constr:({|  co_su := su;
       co_members := m;
       co_attr := a;
       co_sizeof := sz;
       co_alignof := al;
       co_rank := rank;
       co_sizeof_pos := sp;
       co_alignof_two_p := altwo;
       co_sizeof_alignof := sa |} )
  in
 d
end.

Ltac simplify_add_composite_definitions env cl :=  
 match cl with
 | Composite ?id ?su ?m ?a :: ?cl' =>
    let d := constr:(composite_of_def env id su m a)
    in let d' := simplify_composite_of_def d
       in let env' :=  constr:(PTree.set id d' env)
        in let env' := eval simpl in env' in 
       simplify_add_composite_definitions env' cl'
 | nil => constr:(Errors.OK env)
end.

Ltac make_composite_env composites :=
let j := constr:(build_composite_env' composites I)
in let j := eval cbv beta iota zeta delta [
       build_composite_env' build_composite_env
       PTree.empty
      ] in j
 in  match j with context C [add_composite_definitions ?empty ?c] =>
             let cd := simplify_add_composite_definitions empty c in 
             cd
     end.

Ltac make_composite_env0 prog :=
let c := constr:(prog_types prog) in
let c := eval unfold prog, prog_types, Clightdefs.mkprogram in c in 
let comp := match c with
                  | context [build_composite_env' ?comp I] => 
                     let j := eval unfold comp in comp in constr:(j)
                  | _ :: _ => constr:(c)
                  | nil => constr:(c)
                  end in 
let comp' := make_composite_env comp
   in match comp' with Errors.OK ?ce =>
            ce
       end.

Ltac make_compspecs_cenv cenv :=
  let cenv := eval hnf in cenv in
  let cenv := eval simpl in cenv in 
  let cenv_consistent_ := constr:((composite_env_consistent_i composite_consistent cenv ltac:(repeat constructor)): composite_env_consistent cenv) in
  let cenv_legal_fieldlist_ := constr:((composite_env_consistent_i' composite_legal_fieldlist cenv ltac:(repeat constructor)): composite_env_legal_fieldlist cenv) in
  let cenv_legal_su_ := constr:((composite_env_consistent_i (fun c co => composite_complete_legal_cosu_type c (co_members co) = true) cenv ltac:(repeat constructor)): composite_env_complete_legal_cosu_type cenv) in
  let ha_env := eval cbv in (hardware_alignof_env cenv) in
  let Hha_env := constr: (eq_refl: ha_env = hardware_alignof_env cenv) in
  let ha_env_consistent := constr: (hardware_alignof_consistency cenv ha_env cenv_consistent_ Hha_env) in
  let ha_env_complete := constr: (hardware_alignof_completeness cenv ha_env Hha_env) in
  let la_env := eval cbv in (legal_alignas_env cenv ha_env) in
  let Hla_env := constr: (eq_refl: la_env = legal_alignas_env cenv ha_env) in
  let la_env_consistent := constr: (legal_alignas_env_consistency' cenv ha_env la_env cenv_consistent_ Hla_env) in
  let la_env_complete := constr: (legal_alignas_env_completeness' cenv ha_env la_env Hla_env) in
  let la_env_sound := constr: (legal_alignas_soundness cenv ha_env la_env cenv_consistent_ cenv_legal_su_ ha_env_consistent ha_env_complete la_env_consistent la_env_complete) in
  exact (  {| cenv_cs := cenv ;
    cenv_consistent := cenv_consistent_;
    cenv_legal_fieldlist := cenv_legal_fieldlist_;
    cenv_legal_su := cenv_legal_su_;
    ha_env_cs := ha_env;
    ha_env_cs_consistent := ha_env_consistent;
    ha_env_cs_complete := ha_env_complete;
    la_env_cs := la_env;
    la_env_cs_consistent := la_env_consistent;
    la_env_cs_complete := la_env_complete;
    la_env_cs_sound := la_env_sound
   |} ).

Ltac make_compspecs prog :=
  tryif lazymatch type of prog with
  | Clight.program => idtac 
  | ?t => fail 1 "Expected a Clight.program, but "prog" has type" t
 end then idtac 
  else fail "Expected a Clight.program, but "prog" is undefined; did you forget to import the result of clightgen?";
  let cenv := make_composite_env0 prog in
  make_compspecs_cenv cenv.
