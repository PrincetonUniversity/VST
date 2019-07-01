Require Import VST.floyd.proofauto.

Definition tcret_proof retsig (A: rmaps.TypeTree) 
  (Q: forall ts : list Type,
          functors.MixVariantFunctor._functor
            (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred)  :=
  (forall gx ts x (ret : option val),
     (Q ts x (make_ext_rval gx ret)
        && !!step_lemmas.has_opttyp ret (opttyp_of_type retsig)
        |-- !!tc_option_val retsig ret)).

Inductive semax_body_proof :=
| mk_body: forall {Vprog: varspecs} {Gprog: funspecs} {cs: compspecs}
                               {f: function} {id: ident} {fspec: funspec},
    @semax_body Vprog Gprog cs f (id,fspec) -> semax_body_proof
| mk_external: forall (id: ident) retsig {Espec: OracleKind} {ids: list ident} {ef: external_function} 
    {A} {P Q: forall ts : list Type,
          functors.MixVariantFunctor._functor
            (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred},
     tcret_proof retsig A Q ->
    @semax_external Espec ids ef A P Q -> semax_body_proof.

Lemma sub_option_get' {A: Type} (s t: PTree.t A) B (f:A -> option B):
  Forall (fun x => PTree.get (fst x) t = Some (snd x)) (PTree.elements s) ->
  forall i, sub_option (match PTree.get i s with Some x => f x | _ => None end)
                       (match PTree.get i t with Some x => f x | _ => None end).
Proof.
intros.
destruct (s ! i) eqn:?H; [ | apply I].
pose proof (PTree.elements_correct s i H0).
rewrite Forall_forall in H.
apply H in H1.
simpl in H1. rewrite H1. apply sub_option_refl.
Qed.

Lemma sub_option_get {A: Type} (s t: PTree.t A):
  Forall (fun x => PTree.get (fst x) t = Some (snd x)) (PTree.elements s) ->
  forall i, sub_option (PTree.get i s) (PTree.get i t).
Proof.
  intros; specialize (sub_option_get' s t A Some H i); intros.
  destruct (s!i); [simpl; destruct (t!i); inv H0 | ]; trivial.
Qed.   

Lemma tycontext_sub_nofunc_tycontext:
  forall V1 G1 V2 G2,
  (forall id, sub_option (make_tycontext_g V1 G1) ! id (make_tycontext_g V2 G2) ! id) ->
  (forall id, sub_option (make_tycontext_s G1) ! id (make_tycontext_s G2) ! id) ->
  tycontext_sub (nofunc_tycontext V1 G1) (nofunc_tycontext V2 G2).
Proof.
intros.
split3; [ | | split3]; simpl; auto.
intros; destruct ((PTree.empty type) ! id); auto.
split.
intros; apply semax_prog.sub_option_subsumespec; auto.
intros; apply Annotation_sub_refl.
Qed.

Ltac adapt_module module := 
match type of module with @semax_func _ _ _ ?cs _ _ _ =>
eapply @semax_func_subsumption; 
 [ | | eapply (@semax_func_mono _ cs);
    [ | | | apply module]];
  [  |   |
  | intros; apply sub_option_refl | intros; apply sub_option_refl];
 [ 
 | apply @sub_option_get; 
  repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
 | red; red; apply @sub_option_get; 
  repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil]
end;
 apply tycontext_sub_nofunc_tycontext; apply sub_option_get;
   repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil.

Module FunspecOrder <: Orders.TotalLeBool.
  Definition t := (ident * funspec)%type.
  Definition leb := fun x y : (ident * funspec)=> Pos.leb (fst x) (fst y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.  intros. unfold leb. 
    pose proof (Pos.leb_spec (fst a1) (fst a2)).
    pose proof (Pos.leb_spec (fst a2) (fst a1)).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End FunspecOrder.
Module SortFunspec := Mergesort.Sort(FunspecOrder).

Definition ident_of_proof (p: semax_body_proof) : ident :=
 match p with
 | @mk_body _ _ _ _ id _ _ => id
 | @mk_external id _ _ _ _ _ _ _ _ _ => id
 end.

Module BodyProofOrder <: Orders.TotalLeBool.
  Definition t := semax_body_proof.
  Definition leb := fun x y : semax_body_proof=> Pos.leb (ident_of_proof x) (ident_of_proof y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.  intros. unfold leb. 
    pose proof (Pos.leb_spec (ident_of_proof a1) (ident_of_proof a2)).
    pose proof (Pos.leb_spec (ident_of_proof a2) (ident_of_proof a1)).
    inv H; inv H0; auto.
    clear - H2 H3. 
    pose proof (Pos.lt_trans _ _ _ H2 H3).
    apply Pos.lt_irrefl in H. contradiction.
  Qed.
End BodyProofOrder.
Module SortBodyProof := Mergesort.Sort(BodyProofOrder).

Definition Gprog_of_proof (p: semax_body_proof) :=
 match p with
 | @mk_body _ G _ _ _ _ _ => G
 | @mk_external _ _ _ _ _ _ _ _ _ _ => nil
 end.

Fixpoint delete_dups' id f (al: funspecs) : funspecs :=
 match al with
 | (id',f')::al' => if ident_eq id id' then delete_dups' id f al'
                       else (id,f)::delete_dups' id' f' al'
 | nil => (id,f)::nil
 end.

Definition delete_dups (al: funspecs) : funspecs :=
 match al with
 | (id,f)::al' => delete_dups' id f al'
 | nil => nil
 end.

Definition merge_Gprogs_of (module: list semax_body_proof) :=
 delete_dups 
 (SortFunspec.sort
  (List.fold_right (fun m G => Gprog_of_proof m ++ G) (nil: funspecs) module)).

Lemma tycontext_sub_i99:
 forall f Vprog1 Vprog2 Gprog1 Gprog2 Annot,
 (forall id : positive,
   sub_option (make_tycontext_g Vprog1 Gprog1) ! id
    (make_tycontext_g Vprog2 Gprog2) ! id) ->
 (forall id : positive,
   subsumespec (make_tycontext_s Gprog1) ! id (make_tycontext_s Gprog2) ! id) ->
  tycontext_sub (func_tycontext f Vprog1 Gprog1 Annot)
                    (func_tycontext f Vprog2 Gprog2 Annot).
Proof.
intros.
split3; [ | | split3; [ | | split]]; auto.
-
unfold temp_types, func_tycontext, make_tycontext.
intros. destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id); auto.
-
intros. apply Annotation_sub_refl.
Qed.

Lemma subsume_spec_get:
  forall (s t: PTree.t funspec),
   Forall (fun x => subsumespec (Some (snd x)) (t ! (fst x))) (PTree.elements s) ->
   (forall i, subsumespec (s ! i) (t ! i)).
Proof.
intros.
destruct (s ! i) eqn:?H; [ | apply I].
pose proof (PTree.elements_correct s i H0).
rewrite Forall_forall in H.
apply H in H1.
auto.
Qed.

Lemma semax_body_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') V G f spec
(COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
  @semax_body V G CS f spec -> @semax_body V G CS' f spec.
Proof.
  intros. eapply (@semax_body_subsumption' CS CS'); try eassumption. 
  apply tycontext_sub_refl.
Qed. 

Lemma semax_body_subsumption' cs cs' V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (CSUB: cspecs_sub cs cs')
      (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs cs) (snd it) = true) (fn_vars f))
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)):
  @semax_body V' F' cs' f spec.
Proof.
  intros.
  apply (@semax_body_cenv_sub _ _ CSUB); auto.
  eapply semax_body_subsumption; try eassumption.
Qed.

Ltac apply_semax_body L :=
eapply (@semax_body_subsumption' _ _ _ _ _ _ _ _ L);
 [red; red; apply @sub_option_get; 
    repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
 | repeat (apply Forall_cons; [ reflexivity | ]); apply Forall_nil
 | simple apply tycontext_sub_refl ||
  (apply tycontext_sub_i99;
  [ apply sub_option_get;  repeat (apply Forall_cons; [reflexivity | ]);  apply Forall_nil
  | apply subsume_spec_get;
    repeat (apply Forall_cons; [apply subsumespec_refl | ]); apply Forall_nil])].

Ltac semax_func_cons' L H :=
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]);
 first [eapply semax_func_cons;
           [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
           | unfold var_sizes_ok; repeat constructor; try (simpl; rep_omega)
           | reflexivity | LookupID | LookupB | simpl; precondition_closed | 
               apply_semax_body L
           | ]
        | eapply semax_func_cons_ext;
             [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
             | apply H | LookupID | LookupB | apply L |
             ]
        ];
 repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]).

Ltac do_semax_body_proofs x :=
 let x := eval hnf in x in
 match x with
 | mk_external _ _ ?H ?P :: ?y => semax_func_cons' P H; [do_semax_body_proofs y]
 | mk_body ?P :: ?y => semax_func_cons' P I; [do_semax_body_proofs y]
 | nil =>  apply semax_func_nil
 | _ => pose (jj := x)
 end.

Lemma closed_wrt_FF:
 forall {cs: compspecs} S, closed_wrt_vars S FF.
Proof.
 intros. hnf; intros. reflexivity.
Qed.
Lemma closed_wrtl_FF:
 forall {cs: compspecs} S, closed_wrt_lvars S FF.
Proof.
 intros. hnf; intros. reflexivity.
Qed.
Hint Resolve @closed_wrt_FF @closed_wrtl_FF : closed.

