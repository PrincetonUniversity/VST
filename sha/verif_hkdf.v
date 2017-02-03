Require Import floyd.proofauto.
Import ListNotations.
(*Require sha.sha.
Require Import sha.SHA256.*)
Local Open Scope logic.

Require Import sha.hmac_common_lemmas.

Require Import sha.hkdf.
Require Import sha.spec_hmac.
Require Import sha.spec_hkdf.
Require Import sha.hkdf_functional_prog.

Lemma body_hkdf: semax_body Hkdf_VarSpecs Hkdf_FunSpecs 
       f_HKDF HKDF_spec.
Proof.
start_function. 
rename lvar0 into prk. rename lvar1 into plen.
rename H into lenSalt. rename H0 into lenSecret.
assert_PROP (isptr prk /\ field_compatible (tarray tuchar 64) [] prk) by entailer!. destruct H as [Pprk FCprk].
destruct prk; try contradiction. clear Pprk.
assert_PROP (isptr plen /\ field_compatible (tuint) [] plen) by entailer. destruct H as [Pplen FCplen].

unfold data_at_, field_at_.
rewrite field_at_data_at. simpl.
rewrite field_at_data_at. unfold tarray. simpl.
Let vv :reptype (Tarray tuchar (64 - 32) noattr) := list_repeat 64 Vundef.
assert (JMeq (default_val (Tarray tuchar 64 noattr)) (sublist 0 64 vv)).
{ unfold vv. rewrite sublist_list_repeat with (k:=64); try omega. simpl. apply JMeq_refl. }
erewrite  split2_data_at_Tarray with (n1:=32). (* (v':=vv). (list_repeat 64 Vundef):(reptype (Tarray tuchar (64 - 32) noattr))).*)
2: omega.
3: apply JMeq_refl.
3: apply JMeq_refl.
2: eassumption.
normalize. simpl.

freeze [1; 5; 7] FR1.

forward_call (Vptr b i, plen, secret, SECRET, salt, SALT, kv, Tsh).
{ assert (Frame = [FRZL FR1]). subst Frame; reflexivity.
  subst Frame. simpl. cancel.
  rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
  rewrite field_address_offset; trivial.
    simpl. rewrite isptr_offset_val_zero; trivial.
  cancel. eapply derives_trans. apply data_at_memory_block. simpl. trivial. }

(*apply extract_exists_pre. intros extr1.*)

assert (Zlength (HKDF_extract (CONT SALT) (CONT SECRET)) = 32) as ZlengthExtract by apply HMAC_Zlength.
thaw FR1. freeze [1; 2; 5] FR2.

forward_call (out, olen, 
              Vptr b i,
              Build_DATA 32
                  (HKDF_extract (CONT SALT) (CONT SECRET)),
              info, INFO, kv, shmd).
admit. (*VST error: scalar locals as function arguments?*)
admit.
simpl.
cancel.
{ simpl. repeat split; trivial.
  rewrite ZlengthExtract; trivial. omega. omega. }
apply extract_exists_pre. intros x. destruct x. Intros. rename H0 into EXPAND_RES. simpl in *.
unfold expand_out_post, digest_len in EXPAND_RES. rewrite if_false in EXPAND_RES; try omega.
replace (olen + 32 - 1)%Z with (olen + 31)%Z in EXPAND_RES by omega.
destruct (zlt 255 ((olen + 31) / 32)); inv EXPAND_RES.
+ forward_if
  (PROP ( )
   LOCAL (temp _t'3 (Vint (Int.repr 1));
   lvar _prk_len tuint plen; lvar _prk (Tarray tuchar 64 noattr) (Vptr b i); 
   temp _out_key out; temp _out_len (Vint (Int.repr olen)); temp _salt salt;
   temp _salt_len (Vint (Int.repr (LEN SALT))); temp _secret secret;
   temp _secret_len (Vint (Int.repr (LEN SECRET))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (spec_sha.K_vector kv; spec_sha.data_block Tsh (CONT INFO) info;
   spec_sha.data_block Tsh (HKDF_extract (CONT SALT) (CONT SECRET)) (Vptr b i);
   memory_block shmd olen out; FRZL FR2; data_at Tsh tuint (Vint (Int.repr 32)) plen)).
  { congruence. }
  { forward. entailer!. }

  forward_if (`FF).
  { forward. Exists plen. Exists (Vptr b i). Exists 0. entailer!.
    thaw FR2. erewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
    rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
    cancel.
    unfold spec_sha.data_block. rewrite ZlengthExtract. entailer!. }
  { inv H0. } 
  apply semax_ff.

+ forward_if (
  (PROP ( )
   LOCAL (lvar _prk_len tuint plen; lvar _prk (Tarray tuchar 64 noattr) (Vptr b i); 
   temp _out_key out; temp _t'3 (Vint (Int.repr 0)); temp _out_len (Vint (Int.repr olen)); temp _salt salt;
   temp _salt_len (Vint (Int.repr (LEN SALT))); temp _secret secret;
   temp _secret_len (Vint (Int.repr (LEN SECRET))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (spec_sha.K_vector kv; spec_sha.data_block Tsh (CONT INFO) info;
   spec_sha.data_block Tsh (HKDF_extract (CONT SALT) (CONT SECRET)) (Vptr b i);
   spec_sha.data_block shmd (HKDF_expand (HKDF_extract (CONT SALT) (CONT SECRET)) (CONT INFO) olen) out;
   FRZL FR2; data_at Tsh tuint (Vint (Int.repr 32)) plen))). 
  { congruence. }
  { forward. entailer!. }

  forward_if (
  (PROP ( )
   LOCAL (lvar _prk_len tuint plen; lvar _prk (Tarray tuchar 64 noattr) (Vptr b i); 
   temp _out_key out; temp _out_len (Vint (Int.repr olen));
   temp _salt salt; temp _salt_len (Vint (Int.repr (LEN SALT))); temp _secret secret;
   temp _secret_len (Vint (Int.repr (LEN SECRET))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (spec_sha.K_vector kv; spec_sha.data_block Tsh (CONT INFO) info;
   spec_sha.data_block Tsh (HKDF_extract (CONT SALT) (CONT SECRET)) (Vptr b i);
   spec_sha.data_block shmd (HKDF_expand (HKDF_extract (CONT SALT) (CONT SECRET)) (CONT INFO) olen) out;
   FRZL FR2; data_at Tsh tuint (Vint (Int.repr 32)) plen))).
  { elim H0; trivial. }
  { forward. entailer!. }
  forward. Exists plen. Exists (Vptr b i). Exists 1. entailer!. thaw FR2.   
  erewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
  rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
  cancel.
  unfold spec_sha.data_block. rewrite ZlengthExtract. entailer!.
Admitted. (*OK, apart from the admit relating to forward_call*)
(*
 rewrite ZlengthExtract. cancel. Zlength_HKDF_extract. rewrite field_address0_offset by auto with field_compatible. simpl.

cancel.
assert (JMeq (sublist 32 64 vv) (sublist 0 32 vv)).
{ unfold vv. rewrite sublist_list_repeat with (k:=64); try omega. simpl. apply JMeq_refl. }
erewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
cancel.
 simpl. 2: simpl. with (n:=64)(n1:=32). 
2: omega.
3: apply JMeq_refl.
3: apply JMeq_refl.
2: eassumption.
normalize. simpl.

 congruence. simpl.
 simpl.    { repeat split; trivial.
2: simpl.
(*remember (computational_lookup_funspec Delta _HKDF_extract) as spec. symmetry in Heqspec.*)
(*unfold computational_lookup_funspec in Heqspec; simpl in Heqspec.*)
forward_seq.
forward_seq.
apply XX. eapply myConstr. with (witness:=(out, olen, 
              Vptr b i,
              Build_DATA 32
                  (HKFD_extract (CONT SALT) (CONT SECRET)),
              info, INFO, kv, shmd)). econstructor. unfold computational_lookup_funspec. reflexivity. (*slow*)
reflexivity.
reflexivity.
reflexivity.
reflexivity. 
(*
Inductive CFL_OUT' (Delta : tycontext) (id : positive):Prop :=
  CLF_OK: funspec -> CFL_OUT Delta id
| CLF_Error1: type -> CFL_OUT Delta id
| CLF_Error2: CFL_OUT Delta id
| CLF_Error3: type -> CFL_OUT Delta id
| CLF_Error4: funspec -> CFL_OUT Delta id
| CLF_Error5: funspec -> type -> CFL_OUT Delta id
| CLF_Error6: CFL_OUT Delta id
| CLF_Error7: CFL_OUT Delta id.*)
Inductive CFL_OUT :=
  CLF_OK: tycontext -> positive -> funspec -> CFL_OUT
| CLF_Error1: tycontext -> positive -> type -> CFL_OUT
| CLF_Error2: tycontext -> positive -> CFL_OUT
| CLF_Error3: tycontext -> positive -> type -> CFL_OUT
| CLF_Error4: tycontext -> positive -> funspec -> CFL_OUT
| CLF_Error5: tycontext -> positive -> funspec -> type -> CFL_OUT 
| CLF_Error6: tycontext -> positive -> CFL_OUT
| CLF_Error7: tycontext -> positive -> CFL_OUT.

Function computational_lookup_funspec Delta id retty' cc' :=
match (var_types Delta) ! id with
  Some x => CLF_Error1 Delta id x
| None =>
  match (glob_specs Delta) ! id with
           None => CLF_Error2 Delta id
         | Some sp => (*??Which (if any?) of lookup_funspec's arguments are IN and checked,
                          which are OUT??*)
                      match sp with 
                        mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost =>
                        if calling_convention_eq cc cc' then
                           if type_eq retty retty' then
                           match (glob_types Delta) ! id with
                             None => CLF_Error4 Delta id sp
                           | Some t => if type_eq t (type_of_funspec sp) then
                                           CLF_OK Delta id sp (*What are the outs?*)
                                       else CLF_Error5 Delta id sp t
                           end
                           else CLF_Error6 Delta id (*add more info?*)
                        else CLF_Error7 Delta id  (*add more info?*)
                      end
  end
end.

Lemma computational_lookup_funspec_sound Delta id retty cc sp: 
   computational_lookup_funspec Delta id retty cc = CLF_OK Delta id sp ->
   match sp with mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost =>
         global_funspec  Delta id argsig retty cc A Pre Post NEPre NEPost
   end.
Proof. 
unfold computational_lookup_funspec, global_funspec; intros.
destruct sp. destruct f.
destruct ((var_types Delta) ! id); try solve [inv H]. 
split; trivial.
destruct ((glob_specs Delta) ! id); try solve [inv H]. 
destruct f. destruct f. destruct (calling_convention_eq c0 cc); try solve [inv H]. 
subst c0. destruct (type_eq t0 retty); try solve [inv H]. 
subst t0. destruct ((glob_types Delta) ! id); try solve [inv H].
remember  (mk_funspec (l0, retty) cc A0 P0 Q0 P_ne0 Q_ne0).
remember (type_of_funspec f).
destruct (type_eq  t0 t1); try solve [inv H]. inv H. inv H1. split; trivial.
Qed.

Inductive my_semax_call_id1_wow (cs: compspecs) Delta ret id paramty retty 
          (cc:calling_convention) bl P Q R XPost:Prop :=
myConstr: forall {A: rmaps.TypeTree} (witness: functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec nil A) mpred) (Frame: list mpred)
            (*Delta id*) argsig (*retty cc*)
             Pre Post NEPre NEPost
           (*(GLOB: global_funspec  Delta id argsig retty cc A Pre Post NEPre NEPost)*)
           (*Espec {cs: compspecs} P Q R ret (paramty: typelist) (bl: list expr)*)
             (GLOB: computational_lookup_funspec Delta id retty cc = 
                    CLF_OK Delta id (mk_funspec (argsig,retty) cc A Pre Post NEPre NEPost))
             (Post2: environ -> mpred)
             (Ppre: list Prop)
             (Qpre Qnew: list localdef)
             (Qtemp Qactuals Qpre_temp : PTree.t _)
             (Qvar Qpre_var: PTree.t vardesc)
             (B: Type) 
             (Ppost: B -> list Prop)
             (F: B -> val)
             (Rpre: list mpred)
             (Rpost: B -> list mpred)
             (vl : list val)
   (TYret: typeof_temp Delta ret = Some retty)
   (OKretty: check_retty retty)
   (H: paramty = type_of_params argsig)
   (PTREE: local2ptree Q = (Qtemp, Qvar, nil, nil))
   (TC1: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
          |--  (tc_exprlist Delta (argtypes argsig) bl))
   (PRE1: Pre nil witness = PROPx Ppre (LOCALx Qpre (SEPx Rpre)))
   (PTREE': local2ptree Qpre = (Qpre_temp, Qpre_var, nil, nil))
   (MSUBST: force_list (map (msubst_eval_expr Qtemp Qvar) 
                    (explicit_cast_exprlist (argtypes argsig) bl))
                = Some vl)
   (PTREE'': pTree_from_elements (List.combine (var_names argsig) vl) = Qactuals)
   (CHECKTEMP: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) 
           |-- !! Forall (check_one_temp_spec Qactuals) (PTree.elements Qpre_temp))
   (CHECKVAR: ENTAIL Delta, PROPx P (LOCALx Q (SEPx R))
           |-- !! Forall (check_one_var_spec Qvar) (PTree.elements Qpre_var))
   (FRAME: fold_right_sepcon R |-- fold_right_sepcon Rpre * fold_right_sepcon Frame)
   (POST1: Post nil witness = EX vret:B, PROPx (Ppost vret)
                              (LOCALx (temp ret_temp (F vret) :: nil) 
                              (SEPx (Rpost vret))))
   (DELETE: delete_temp_from_locals ret Q = Qnew)
   (H0: Post2 = EX vret:B, PROPx (P++ Ppost vret) (LOCALx (temp ret (F vret) :: Qnew)
             (SEPx (Rpost vret ++ Frame))))
   (PPRE: fold_right_and True Ppre)
   (HXPost: XPost = normal_ret_assert Post2),
   my_semax_call_id1_wow cs Delta ret id paramty retty cc bl P Q R XPost.

Lemma XX: forall cs Espec Delta ret id bl paramty retty cc P Q R Post,
  my_semax_call_id1_wow cs Delta ret id paramty retty cc bl P Q R Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) 
         (Scall (Some ret)
                (Evar id (Tfunction paramty retty cc))
                 bl)
         Post.
Proof. intros. inv H.
apply computational_lookup_funspec_sound in GLOB.
eapply semax_call_id1_wow; eauto.
Qed.
(*
fun (Delta : tycontext) (id : positive) (argsig : list (ident * type)) 
  (retty : type) (cc : calling_convention) (A : rmaps.TypeTree)
  (Pre
   Post : forall ts : list Type,
          functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A))
            mpred) (NEPre : super_non_expansive Pre) (NEPost : super_non_expansive Post) =>
(var_types Delta) ! id = None /\
(glob_specs Delta) ! id = Some (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost) /\
(glob_types Delta) ! id =
Some (type_of_funspec (mk_funspec (argsig, retty) cc A Pre Post NEPre NEPost))


Print global_funspec.

Once we know we're in the right case, the general principle of ltacs
should not be 
eapply semaxZZ; [ tac1 | tac2 .... | tac n]

but let fresh hyp1:= the Prop we expect tac1 to establish, (plus a tactic/compuattion to get it)
     let fresh hyp2:= the Prop we epect tac2 to establish
     :
     in eapply (semaxZZ hyp1 hyp2) ; clear hyp1 ... hypn.

Thus, first establish the SC's then apply the rule.


Print global_funspec.
Then add better error message for global_funspec:

id not found in globspecs

Inductive Forward_call_no_match  : Prop := .

Lemma XX: forall cs Espec Delta e P Q R Post,
  match e with
  Scall (Some ret)
             (Evar id (Tfunction paramty retty cc))
             bl => (*semax_call_id1_wow*)
              my_semax_call_id1_wow cs Delta ret id paramty retty cc bl P Q R Post
(*    
| Ssequence (Scall (Some ret')
             (Evar id (Tfunction paramty retty' cc))
             bl)
      (Sset ret (Ecast (Etempvar ret' retty') retty) =>
        (*case semax_call_id1_x_wow*)*)
| _ => Forward_call_no_match
  end ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) e Post.
Proof. intros. destruct e; try solve [inv H].
destruct o; try solve[inv H].
destruct e; try solve[inv H].
destruct t; try solve[inv H].
inv H.
eapply semax_call_id1_wow; eauto.
Qed.
(*
Definition fact_spec' :=
  DECLARE _fact
   WITH n:int
   PRE [ _n OF tint]
         PROP (Int.le Int.zero n /\ Int.lt n Int.repr Int.max_signed)
         LOCAL (temp _n (Vint n)))
         SEP(()
  POST [ tint ] 
          PROP ()
          LOCAL (temp ret_temp (Vint (FACint n)))
          SEP().
*)


apply GLOB. 5: apply TC1. id argsig retty cc Pre Post0 NEPre NEPost GLOB); try eassumption.
destruct
eapply (@semax_call_id1_wow A Delta id argsig retty cc Pre Post0 NEPre NEPost GLOB); try eassumption.
destruct
SearchAbout map.
*)
(*
Axiom CS: CompSpecs = spec_hmac.CompSpecs. 
Lemma change_compspecs_datablock:
  @spec_sha.data_block sha.spec_hmac.CompSpecs  =
  @spec_sha.data_block hkdf_compspecs.CompSpecs.
Proof.
extensionality gfs. rewrite CS. trivial.
Qed.
*)
Lemma body_hkdf: semax_body Hkdf_VarSpecs Hkdf_FunSpecs 
       f_HKDF HKDF_spec.
Proof.
start_function. 
rename lvar0 into prk. rename lvar1 into plen.
rename H into lenSalt. rename H0 into lenSecret.
assert_PROP (isptr prk /\ field_compatible (tarray tuchar 64) [] prk) by entailer!. destruct H as [Pprk FCprk].
destruct prk; try contradiction. clear Pprk.
unfold data_at_, field_at_.
rewrite field_at_data_at. simpl.
rewrite field_at_data_at. unfold tarray. simpl.
Let vv :reptype (Tarray tuchar (64 - 32) noattr) := list_repeat 64 Vundef.
assert (JMeq (default_val (Tarray tuchar 64 noattr)) (sublist 0 64 vv)).
{ unfold vv. rewrite sublist_list_repeat with (k:=64); try omega. simpl. apply JMeq_refl. }
erewrite  split2_data_at_Tarray with (n1:=32). (* (v':=vv). (list_repeat 64 Vundef):(reptype (Tarray tuchar (64 - 32) noattr))).*)
2: omega.
3: apply JMeq_refl.
3: apply JMeq_refl.
2: eassumption.
normalize. simpl.

freeze [1; 5; 7] FR1.

forward_call (Vptr b i, plen, secret, SECRET, salt, SALT, kv, Tsh).
{ (* assert (Frame = [data_at Tsh (Tarray tuchar 32 noattr) (sublist 32 64 vv)
    (field_address0 (Tarray tuchar 64 noattr) [ArraySubsc 32]
     (field_address (Tarray tuchar 64 noattr) [] (Vptr b i))) *
     (data_block Tsh (CONT INFO) info * memory_block shmd olen out)]).*)
   assert (Frame = [FRZL FR1]).
   subst Frame; reflexivity.
  subst Frame. simpl. cancel. 
  rewrite sepcon_comm.
  apply sepcon_derives; clear H0.
  + unfold data_at_, field_at_. rewrite field_at_data_at. cancel.
  + unfold tarray in FCprk.
    unfold field_address.
    destruct (field_compatible_dec (Tarray tuchar 64 noattr) [] (Vptr b i)); try contradiction. clear f.
    simpl. rewrite Int.add_zero. eapply derives_trans. apply data_at_memory_block. trivial. }

apply extract_exists_pre. intros extr1.
(*repeat flatten_sepcon_in_SEP. *)
assert (Zlength (HKFD_extract (CONT SALT) (CONT SECRET)) = 32) by apply HMAC_Zlength.
thaw FR1. freeze [1; 2; 5] FR2.
(*remember (computational_lookup_funspec Delta _HKDF_extract) as spec. symmetry in Heqspec.*)
(*unfold computational_lookup_funspec in Heqspec; simpl in Heqspec.*)
forward_seq.
forward_seq.
apply XX. eapply myConstr. with (witness:=(out, olen, 
              Vptr b i,
              Build_DATA 32
                  (HKFD_extract (CONT SALT) (CONT SECRET)),
              info, INFO, kv, shmd)). econstructor. unfold computational_lookup_funspec. reflexivity. (*slow*)
reflexivity.
reflexivity.
reflexivity.
reflexivity. 
entailer. admit. (*??*) 
( out, olen, 
              Vptr b i,
              Build_DATA 32
                  (HKFD_extract (CONT SALT) (CONT SECRET)),
              info, INFO, kv, shmd)

reflexivity.
eapply semax_call_id1_wow.
destruct spec; try inversion Heqspec. simpl in Heqspec.
unfold Delta in Heqspec; simpl in Heqspec.



forward_seq.
forward_seq.
apply XX. econstructor.
{ repeat split; try reflexivity. }
check_result_type.
check_result_type.
reflexivity.
reflexivity. Locate lookup_funspec. 
entailer. simpl.
simpl.
simpl. apply Coq.Init.Logic.I. Locate int. Check Vint.
  split. reflexivity.
  reflexivity.

Ltac check_result_type := 
   first [reflexivity | elimtype  Result_type_in_funspec_different_from_call_statement].
{ split. reflexivity.
  split. reflexivity.
  reflexivity.
simpl. reflexivity.
simpl.
check_result_type.
 | apply Coq.Init.Logic.I | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck

(*

Ltac forward_call_id1_x_wow A witness Frame H :=
 eapply (@semax_call_id1_x_wow A witness Frame _ _ _ _ _ _ _ _ _ H);
 clear H; try clear Frame;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity 
 | (clear; let H := fresh in intro H; inversion H)
 | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | (*cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]*)idtac
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id1_y_wow A witness Frame H :=
 eapply (@semax_call_id1_y_wow A witness Frame _ _ _ _ _ _ _ _ _ H);
 clear H; try clear Frame;
 [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity 
 | (clear; let H := fresh in intro H; inversion H)
 | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | (*cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]*)idtac
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id1_wow A witness Frame H :=
 eapply (@semax_call_id1_wow A witness Frame _ _ _ _ _ _ _ _ _ H);
 clear H; try clear Frame;
 [ check_result_type
 | apply Coq.Init.Logic.I | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | (*cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]*) idtac
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id01_wow A witness Frame H :=
 eapply (@semax_call_id01_wow A witness Frame _ _ _ _ _ _ _ _ _ H);
 clear H; try clear Frame;
 [ apply Coq.Init.Logic.I | reflexivity
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | (*cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]*)idtac
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac forward_call_id00_wow A witness Frame H :=
 eapply (@semax_call_id00_wow A witness Frame _ _ _ _ _ _ _ _ _ H);
 clear H; try clear Frame;
 [ check_result_type | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | (*cbv beta iota zeta;
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0;
    first [reflexivity | extensionality; simpl; reflexivity]*) idtac
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Ltac fwd_call' A witness H := 
 first[ eapply semax_seq';
         [clear_Delta_specs; clear_MORE_POST;
          let Frame := fresh "Frame" in
          evar (Frame: list (mpred));
          first [forward_call_id1_wow A witness Frame H
           | forward_call_id1_x_wow A witness Frame H
           | forward_call_id1_y_wow A witness Frame H
           | forward_call_id01_wow A witness Frame H
           | forward_call_id00_wow A witness Frame H
           ]
         | clear H; after_forward_call]
     | rewrite <- seq_assoc; fwd_call' A witness H].

Ltac fwd_call witness :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat match goal with 
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end;
match goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  match C with context [Scall _ (Evar ?id _) _] =>
   refine (modusponens (global_funspec Delta id _ _ _ _ _ _ _ _) _ _ _);
  [ eapply lookup_funspec; 
    [check_function_name 
    | lookup_spec_and_change_compspecs CS id
    | find_spec_in_globals']
  | let H := fresh in intro H;
    match type of H with global_funspec _ _ _ _ _ ?A _ _ _ _ =>
     first [unify A (rmaps.ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             elimtype False 
           | fwd_call' A witness H]
    end
  ]
  end
end.

Tactic Notation "forward_call" constr(witness) := fwd_call witness.
*)
(*cbv beta iota zeta; extensionality rho.
   repeat rewrite exp_uncurry.
   try rewrite no_post_exists. repeat rewrite exp_unfold.
apply exp_congr. intros ?vret. f_equal. reflexivity. f_equal. reflexivity.

unfold Warning_perhaps_funspec_postcondition_needs_EX_outside_PROP_LOCAL_SEP.
econstructor.
Exists Int.one. apply derives_refl. trivial.
*)


(*Ltac check_typecheck ::= fail 1000.*)
(* first [goal_has_evars; idtac |
 try apply local_True_right; 
 entailer!]. *)(*;
 match goal with
 | |- typecheck_error (deref_byvalue ?T) =>
       elimtype (Function_arguments_include_a_memory_load_of_type T)
 | |- _ => idtac
 end].*)(*
Ltac forward_call_id00_wow A witness Frame H ::= fail 1000.
Ltac forward_call_id01_wow A witness Frame H ::= fail 2000.
*)
Ltac forward_call_id1_y_wow A witness Frame H ::=
 eapply (@semax_call_id1_y_wow A witness Frame _ _ _ _ _ _ _ _ _ H);
 clear H; try clear Frame
(* [ check_result_type | check_result_type
 | apply Coq.Init.Logic.I | apply Coq.Init.Logic.I | reflexivity 
 | (clear; let H := fresh in intro H; inversion H)
 | check_parameter_types
 | check_prove_local2ptree
 | idtac
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | prove_delete_temp
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ]*).
 (*
Ltac after_forward_call ::= idtac.
    cbv beta iota delta [delete_temp_from_locals]; 
    simpl ident_eq; cbv beta iota zeta;
    repeat match goal with |- context [eq_rec_r ?A ?B ?C] => 
              change (eq_rec_r A B C) with B; cbv beta iota zeta
            end;
    unfold_app;
    try (apply extract_exists_pre; intros _);
    match goal with
        | |- semax _ _ _ _ => idtac 
        | |- unit -> semax _ _ _ _ => intros _ 
    end;
    repeat (apply semax_extract_PROP; intro);
    cleanup_no_post_exists;
    abbreviate_semax;
    try fwd_skip.*)

Ltac fwd_call' A witness H ::= 
 first[ eapply semax_seq';
         [clear_Delta_specs; clear_MORE_POST;
          let Frame := fresh "Frame" in
          evar (Frame: list (mpred));
          first [(*forward_call_id1_wow A witness Frame H
           | forward_call_id1_x_wow A witness Frame H*)
            forward_call_id1_y_wow A witness Frame H
(*           | forward_call_id01_wow A witness Frame H
           | forward_call_id00_wow A witness Frame H*)
           ]
         | clear H; idtac (*after_forward_call*)]
     | rewrite <- seq_assoc; fwd_call' A witness H].


forward_call (out, olen, 
              Vptr b i,
              Build_DATA 32
                  (HKFD_extract (CONT SALT) (CONT SECRET)),
              info, INFO, kv, shmd); simpl.

check_result_type. check_result_type.
 apply Coq.Init.Logic.I. apply Coq.Init.Logic.I. reflexivity.
 (clear; let H := fresh in intro H; inversion H).
 check_parameter_types.
 check_prove_local2ptree.
 check_typecheck. admit.
 check_funspec_precondition.
 check_prove_local2ptree.
 check_cast_params. reflexivity. intros. admit. (*Forall_pTree_from_elements.*)
 admit. (*Forall_pTree_from_elements.*)
 unfold fold_right_sepcon at 1 2; cancel. admit.
 cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ].
 prove_delete_temp.
 prove_delete_temp.
 unify_postcondition_exps.
 unfold fold_right_and; repeat rewrite and_True; auto. admit.

Ltac check_typecheck ::=
 first [goal_has_evars; idtac |
 try apply local_True_right; 
 entailer!;
 match goal with
 | |- typecheck_error (deref_byvalue ?T) =>
       elimtype (Function_arguments_include_a_memory_load_of_type T)
 | |- _ => idtac
 end].
try apply local_True_right. entailer!.
goal_has_evars; idtac.
check_typecheck.
first [goal_has_evars; idtac |
 try apply local_True_right; 
 entailer!]. *)(*;
 match goal with
 | |- typecheck_error (deref_byvalue ?T) =>
       elimtype (Function_arguments_include_a_memory_load_of_type T)
 | |- _ => idtac
 end].

check_typecheck.
first [goal_has_evars; idtac |
 try apply local_True_right; 
 entailer!;
 match goal with
 | |- typecheck_error (deref_byvalue ?T) =>
       elimtype (Function_arguments_include_a_memory_load_of_type T)
 | |- _ => idtac
 end].
check_typecheck.
2: simpl.

Print data_at_.

simpl. simpl. trivial. cancel. Int.plus_o_r. unfold offset_val.
Ltac fwd_call1  :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat match goal with 
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end.
Ltac fwd_call2 witness  :=
match goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  match C with context [Scall _ (Evar ?id _) _] =>
   refine (modusponens (global_funspec Delta id _ _ _ _ _ _ _ _) _ _ _);
  [ eapply lookup_funspec; 
    [check_function_name 
    | lookup_spec_and_change_compspecs CS id
    | find_spec_in_globals']
  | let H := fresh in intro H;
    match type of H with global_funspec _ _ _ _ _ ?A _ _ _ _ =>
     first [unify A (rmaps.ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             elimtype False 
           | idtac (*fwd_call' A witness H*)]
    end
  ]
  end
end.
fwd_call1.
fwd_call2 z.
let Frame := fresh "Frame" in
          evar (Frame: list (mpred)).
Let A :=(rmaps.ConstType (val * val * DATA * val * DATA * val * share)).
eapply semax_seq.
eapply semax_post.
Focus 2. assert ({| cc_vararg := false; cc_unproto := true; cc_structret := false |} = cc_default). admit.
rewrite H0.  
eapply (@semax_call_id1_x_wow A z Frame _ _ _ _ _ _ _ _ _ H).
eapply semax_call_id1_wow. simpl.
 check_result_type.
 | apply Coq.Init.Logic.I | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | cbv beta iota zeta; extensionality rho; 
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].

Check semax_call_id00_wow.
Print HKDF_extract_spec.
Ltac fwd_call1  :=
 try match goal with
      | |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip
      end;
 repeat match goal with 
  | |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
      rewrite <- seq_assoc
 end.
fwd_call1.
Ltac fwd_call2 witness  :=
match goal with |- @semax ?CS _ ?Delta _ (Ssequence ?C _) _ =>
  match C with context [Scall _ (Evar ?id _) _] =>
   refine (modusponens (global_funspec Delta id _ _ _ _ _ _ _ _) _ _ _);
  [ eapply lookup_funspec; 
    [check_function_name 
    | lookup_spec_and_change_compspecs CS id
    | find_spec_in_globals']
  | let H := fresh in intro H;
    match type of H with global_funspec _ _ _ _ _ ?A _ _ _ _ =>
     first [unify A (rmaps.ConstType Ridiculous); (* because [is_evar A] doesn't seem to work *)
             elimtype False 
           | idtac (*fwd_call' A witness H*)]
    end
  ]
  end
end.
Tactic Notation "forward_call2" constr(witness) := fwd_call2 witness.
forward_call2 z.
eapply semax_seq'. clear_Delta_specs; clear_MORE_POST.
let Frame := fresh "Frame" in
          evar (Frame: list (mpred)).
Let A :=(rmaps.ConstType (val * val * DATA * val * DATA * val * share)).
eapply semax_seq'. 
forward_call_id1_y_wow A z Frame H.
Check @semax_call_id01_wow. Check (rmaps.ConstType (val * val * DATA * val * DATA * val * share)).
Ltac fwd_call' A witness H := 
 first[ eapply semax_seq';
         [clear_Delta_specs; clear_MORE_POST;
          let Frame := fresh "Frame" in
          evar (Frame: list (mpred));
          first [forward_call_id1_wow A witness Frame H
           | forward_call_id1_x_wow A witness Frame H
           | forward_call_id1_y_wow A witness Frame H
           | forward_call_id01_wow A witness Frame H
           | forward_call_id00_wow A witness Frame H
           ]
         | clear H; after_forward_call]
     | rewrite <- seq_assoc; fwd_call' A witness H].

forward_seq.
forward_seq.
forward_seq.
eapply semax_post.
Focus 2. 
forward_call (prk, 
              secret, SECRET,
              salt, SALT, kv, Tsh).
rename lvar0 into pad. rename lvar1 into ctxkey.
remember (salt,SALT,secret, SECRET,kv,shmd,out) as z.
rewrite <- change_compspecs_datablock.
assert (olen = 32). admit. subst olen.
assert (hmac._HMAC = _HMAC). reflexivity. rewrite <- H.
 assert (CompSpecs = spec_hmac.CompSpecs). admit. rewrite H0.
Print HMAC_spec. 

Lemma body_hkdf_extend: semax_body HkdfVarSpecs HkdfFunSpecs 
       f_HKDF_extract HKDF_extract_spec.
Proof.
start_function. 
remember (salt,SALT,secret, SECRET,kv,shmd,out) as z.
rewrite <- change_compspecs_datablock.
assert (olen = 32). admit. subst olen.
assert (hmac._HMAC = _HMAC). reflexivity. rewrite <- H.
 assert (CompSpecs = spec_hmac.CompSpecs). admit. rewrite H0.
Print HMAC_spec. 

forward_call (salt,SALT,secret, SECRET,kv,shmd,out).
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        kv:val, shmd: share, md: val
continue here.

Lemma change_compspecs_t_struct_hmacctxstate_st:
  @data_at_ spec_hmac.CompSpecs Tsh t_struct_hmac_ctx_st =
  @data_at_ spec_hkdf.CompSpecs Tsh t_struct_hmac_ctx_st.
Proof.
extensionality gfs.
Admitted.

Hint Rewrite change_compspecs_t_struct_SHA256state_st : norm.
Hint Rewrite change_compspecs_t_struct_hmacctxstate_st: norm.

Lemma body_hkdf_expand: semax_body HkdfVarSpecs HkdfFunSpecs 
       f_HKDF_expand HKDF_expand_spec.
Proof.
start_function. rename lvar0 into previous.
rename lvar1 into hmac. rename lvar2 into ctr. 
freeze [0;1;2;3;4;5;6] FR1.
forward. forward. forward. forward.
forward_if 
  (PROP (Int.unsigned (Int.repr (olen + 32)) >= Int.unsigned (Int.repr olen) )
   LOCAL (temp _t'1 (force_val
  (sem_cast_i2i IBool Unsigned
     (Val.of_bool
        (Int.ltu (Int.repr 255)
           (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32))))));
   temp _n (Vint (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32)));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (Int.repr 0));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).
{ forward. admit. (*case Int.unsigned (Int.repr (olen + 32)) < Int.unsigned (Int.repr olen)*) }
{ forward. entailer!. }
Intros. rename H into LEN.
rewrite sem_cast_i2i_correct_range; [simpl | apply semax_straight.is_int_of_bool].
forward_if 
  (PROP (255 >= Int.unsigned (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32)) )
   LOCAL (temp _n (Vint (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32)));
   temp _ret (Vint (Int.repr 0)); temp _done (Vint (Int.repr 0));
   temp _digest_len (Vint (Int.repr 32)); lvar _ctr tuchar ctr;
   lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).
{ (*Case 255 <
    Int.unsigned (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32))*)
   rename H into N. forward. admit. }
{ forward. entailer!. }
Intros. rename H into N.
thaw FR1. 
Time assert_PROP (isptr prk) as isPtrPrk by entailer!. destruct prk; try contradiction.
(*remember (hmac, Vptr b i, spec_hmac.LEN PRK, spec_hmac.CONT PRK, kv, spec_hmac.HMACabs nil nil nil) as z.*)
(*c : val, k:val, l:Z, key:list Z, kv:val, h1:hmacabs*)

assert (@data_at_ spec_hkdf.CompSpecs Tsh (Tstruct _hmac_ctx_st noattr) = 
        @data_at_ spec_hmac.CompSpecs Tsh (Tstruct _hmac_ctx_st noattr)).  admit.
(*rewrite H.*)
assert (@data_block CompSpecs Tsh (CONT PRK) = 
        @data_block spec_hmac.CompSpecs Tsh (CONT PRK)).  admit.
rewrite H1.
assert (Tstruct _hmac_ctx_st noattr = t_struct_hmac_ctx_st). admit.
assert (tptr (Tstruct _hmac_ctx_st noattr) = tptr t_struct_hmac_ctx_st). rewrite H2; trivial. 
rewrite H3.
forward_call (hmac, Vptr b i, spec_hmac.LEN PRK, spec_hmac.CONT PRK, kv, spec_hmac.HMACabs nil nil nil) .
{ rewrite H2. simpl. entailer!. cancel. }

contineu here.


 (*Case 255 >= Int.unsigned (Int.divu (Int.repr (olen + 32 - 1)) (Int.repr 32))*)
  rename H into N. forward. rewrite sem_cast_i2i_correct_range apply typed_true_cmp in H.
  (PROP ( )
   LOCAL (temp _n
            (Vint
               (Int.divu
                  (Int.sub (Int.add (Int.repr olen) (Int.repr 32)) (Int.repr 1))
                  (Int.repr 32))); temp _ret (Vint (Int.repr 0));
   temp _done (Vint (Int.repr 0)); temp _digest_len (Vint (Int.repr 32));
   lvar _ctr tuchar ctr; lvar _hmac (Tstruct _hmac_ctx_st noattr) hmac;
   lvar _previous (tarray tuchar 64) previous; temp _out_key out;
   temp _out_len (Vint (Int.repr olen)); temp _prk prk;
   temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK))); 
   temp _info info; temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
   gvar sha._K256 kv)  SEP (FRZL FR1)).

Lemma body_hkdf: semax_body HkdfVarSpecs HkdfFunSpecs 
       f_HKDF HKDF_spec.
Proof.
start_function. rename lvar0 into prk. rename lvar1 into plen.
forward_call (prk, plen,
              secret, SECRET,
              salt, SALT, kv, Tsh).
rename lvar0 into pad. rename lvar1 into ctxkey.
apply initbodyproof.
Qed.

Lemma initbodyproof Espec c k l key kv h1 pad ctxkey:
@semax CompSpecs Espec (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)
  (PROP  ()
   LOCAL  (lvar _ctx_key (tarray tuchar 64) ctxkey;
           lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k;
           temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  (data_at_ Tsh (tarray tuchar 64) ctxkey;
         data_at_ Tsh (tarray tuchar 64) pad;
         K_vector kv; initPre c k h1 l key))
  (Ssequence (fn_body f_HMAC_Init) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP  (hmacstate_ (hmacInit key) c; initPostKey k key; K_vector kv)))
     ((EX  v : val,
       local (locald_denote (lvar _pad (tarray tuchar 64) v)) &&
       `(data_at_ Tsh (tarray tuchar 64) v))%assert *
      (EX  v : val,
       local (locald_denote (lvar _ctx_key (tarray tuchar 64) v)) &&
       `(data_at_ Tsh (tarray tuchar 64) v))%assert)).
Proof. abbreviate_semax.
freeze [1; 2; 3] FR1. simpl.
Time forward. (*0.8 versus 1.3*)
 
Time assert_PROP (isptr ctxkey) as Pckey by entailer!. (*0.7*) 
apply isptrD in Pckey; destruct Pckey as [ckb [ckoff PcKey]]. 
  (*Issue subst ctxkey. fails*) rewrite PcKey in *.

(*isolate branch if (key != NULL) *)
apply seq_assoc.
(*from init_part1:
Definition initPostKeyNullConditional r (c:val) (k: val) h key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 
                   then (hmacstate_PreInitNull key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st keyedHMS c) *
                     (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      ctxkey)  *
                     (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                      (Vptr b ofs)))
  | _ => FF
  end.*)
(*remember (EX  cb : block,
                 (EX  cofs : int,
                   (EX  r : Z, 
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (temp _reset (Vint (Int.repr r));
                      lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); 
                      lvar _pad (tarray tuchar 64) pad;
                      temp _ctx c; temp _key k; temp _len (Vint (Int.repr l));
                      gvar sha._K256 kv)
                    SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                    initPostKeyNullConditional r c k h1 key (Vptr ckb ckoff);
                    K_vector kv)))) as PostKeyNull. *)
forward_seq. instantiate (1:= PostKeyNull c k pad kv h1 l key ckb ckoff).
{  assert (DD: Delta= initialized _reset Delta) by reflexivity.
   rewrite DD.
   eapply semax_pre_simple.
   2: eapply hmac_init_part1; eassumption.
   thaw' FR1. Time entailer!. (*2.2 versus 2.3*) }
(*subst PostKeyNull.*)
unfold PostKeyNull. Intros cb cofs r.
(*Time normalize. (*2.3*)*)
unfold POSTCONDITION, abbreviate. subst c.
rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.
(*from init_part2:
Definition postResetHMS (iS oS: s256state): hmacstate :=
  (default_val t_struct_SHA256state_st, (iS, oS)).
Definition initPostResetConditional r (c:val) (k: val) h key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else !!(Forall isbyteZ key) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS iS oS) c) *
                        (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b ofs)))
  | _ => FF
  end.*)
remember (EX shaStates:_ ,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           =(fst shaStates) /\
                  s256_relate (fst shaStates) (fst (snd shaStates)) /\
                  outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                          = (fst (snd (snd shaStates))) /\ 
                  s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
          LOCAL  (lvar _pad (tarray tuchar 64) pad; 
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); 
                  temp _ctx (Vptr cb cofs); temp _key k;
                  temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
          SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff); 
                initPostResetConditional r (Vptr cb cofs) k h1 key (fst (snd shaStates)) (snd (snd (snd shaStates)));
                K_vector kv))
  as PostResetBranch.
clear FR1.
eapply semax_seq. instantiate (1:=PostResetBranch).
{ eapply semax_pre_post.
  Focus 3 . apply init_part2; try eassumption.
  apply andp_left2. apply derives_refl.
  intros ? ?. apply andp_left2. apply derives_refl. }

{ (*Continuation after if (reset*)
  subst PostResetBranch.
  simpl update_tycon.
  apply semax_extensionality_Delta with (Delta). 
  apply tycontext_sub_refl.
  apply extract_exists_pre; intros [iSA [iS [oSA oS]]]. simpl.
  assert_PROP (is_pointer_or_null k) as Ptr_null_k by entailer!.
  destruct k; simpl in Ptr_null_k; try contradiction.
  { (*Case key==null*) 
    subst i.
    destruct R; subst r; simpl.
    2: solve [apply semax_pre with (P':=FF); try entailer!; try apply semax_ff].
    freeze [0; 1; 3] FR2.
    Time normalize. (*5.7*)
    rename H into InnerRelate.
    rename H0 into OuterRelate.
    unfold hmacstate_PreInitNull.
    Intros s v.
    rename H into Hs.
    unfold hmac_relate_PreInitNull in Hs. 
    clear InnerRelate OuterRelate iS oS.
    destruct h1.
    destruct Hs as [IREL [OREL [ILEN [OLEN [ISHA OSHA]]]]].
    destruct s as [mdS [iS oS]]. 

(* Issue: why is update_reptype not simplifying? *) 
     match goal with |- context [@upd_reptype ?cs ?t ?gfs ?x ?v] => 
           change (@upd_reptype cs t gfs x v) with (v,(iS,oS)) end.
     simpl in *.

     Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
       as FC_cb by entailer!. (*1.8 versus 3.9*)
     assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. right; left. reflexivity.
     assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. left. reflexivity.

     Time unfold_data_at 1%nat. (*0.8, was slow*)
     rewrite (field_at_data_at _ _ [StructField _i_ctx]).
     (*VST Issue: why does rewrite field_at_data_at at 2 FAIL, but focus_SEP 3; rewrite field_at_data_at at 1. SUCCEED???
        Answer: instead of using "at 2", use the field-specificer in the line above.*)
     rewrite field_address_offset by auto with field_compatible. 
    
     freeze [0; 3] FR3.  
     Time forward_call ((Tsh, Tsh),
             Vptr cb cofs,
             Vptr cb (Int.add cofs (Int.repr 108)),
             mkTrep t_struct_SHA256state_st iS, 
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st).
     (*5.9 versus 13*)
     { rewrite sepcon_comm.
       rewrite (field_at_data_at _ _ [StructField _md_ctx]). 
       rewrite field_address_offset by auto with field_compatible.
       apply sepcon_derives. 
         eapply derives_trans. apply data_at_memory_block. apply derives_refl'. f_equal. 
         apply isptr_offset_val_zero; simpl; trivial.
       Time cancel. (*0 versus 2*)
     }

     freeze [0; 1; 2] FR4. 
     Time forward. (*return*) (* 3 versus 13*) (*Issue : leaves a somewhat messy subgoal*)
     Exists (Vptr ckb ckoff) pad.
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     Time entailer!. (*1.6 versus 7.4*)
     unfold hmacstate_, hmac_relate.
      Exists (iS, (iS, oS)).
      simpl. Time entailer!. (*1.9 versus 5.6*)

     unfold_data_at 1%nat.
     rewrite (field_at_data_at _ _ [StructField _md_ctx]).
     rewrite (field_at_data_at _ _ [StructField _i_ctx]).
      rewrite field_address_offset by auto with field_compatible.
      rewrite field_address_offset by auto with field_compatible.
      simpl; rewrite Int.add_zero. 
      change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
      thaw FR4. thaw FR3. thaw FR2. 
      Time cancel. (*1.6 versus 0.7*)
  }

  { (*k is Vptr, key!=NULL*)
    freeze [0;1;3] FR5.
    destruct R as [R | R]; rewrite R; simpl. 
    solve [apply semax_pre with (P':=FF); try entailer; try apply semax_ff].
    Intros.
    rename H0 into InnerRelate.
    rename H2 into OuterRelate. rename H3 into isbyteKey.
    unfold postResetHMS. simpl.
    freeze [0; 2] FR6. 
    Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_cb by entailer!. (*2.8*)
    assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. right; left. reflexivity.
    assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. left. reflexivity.

    unfold_data_at 1%nat. 
    freeze [0; 3] FR7. 
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address_offset by auto with field_compatible.
    simpl; rewrite Int.add_zero. 
   
    Time forward_call ((Tsh, Tsh),
             Vptr cb cofs,
             Vptr cb (Int.add cofs (Int.repr 108)),
             mkTrep t_struct_SHA256state_st iS,
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st).
    (* 4.7 versus 14.7 *)
    { rewrite sepcon_comm.
      apply sepcon_derives. 
          eapply derives_trans. apply data_at_memory_block. apply derives_refl.
          Time cancel. (*0 versus 2*) 
    }
    freeze [0; 1; 2] FR8. 
    Time forward. (*return*) (*3.4 versus 17*) (*Issue: leaves messy subgoal*) 
    Exists (Vptr ckb ckoff) pad. 
    Time entailer!. (* 1.2 versus 9*)
    unfold data_block, hmacstate_, hmac_relate.
    Exists (iS, (iS, oS)).
    change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z key)))
       with (@data_at CompSpecs Tsh (tarray tuchar (@Zlength Z key))).
    change (Tarray tuchar 64 noattr) with (tarray tuchar 64). simpl.
    Time entailer!. (*2.9*)
      unfold s256a_len, innerShaInit, outerShaInit.
           repeat rewrite Zlength_mkArgZ,
           map_length, mkKey_length. split; reflexivity.
    unfold_data_at 1%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]).
      rewrite (field_at_data_at _ _ [StructField _i_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address_offset by auto with field_compatible.
    simpl; rewrite Int.add_zero. 
    thaw FR8. thaw FR7. thaw FR6. thaw FR5.
    Time cancel. (*1.7 versus 1.2 penalty when melting*) 
  }
} 
Time Qed. (*25 versus 49*)

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
rename lvar0 into pad. rename lvar1 into ctxkey.
apply initbodyproof.
Qed.
*)