Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.veric Require Import env Clight_core Clight_seplog.
From VST.typing Require Export type.
From VST.typing Require Import programs singleton bytes.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.

Section function.
  Context `{!typeG OK_ty Σ} {cs : compspecs} {A : Type}.
  Record fn_ret := FR {
    (* return type (rc::returns) *)
    fr_rty : type;
    (* postcondition (rc::ensures) *)
    fr_R : iProp Σ;
  }.
  Definition mk_FR (rty : type) (R : iProp Σ) := FR rty R.


  (* The specification of a function is given by [A → fn_params].
     The full specification roughly looks like the following:
     ∀ x : A, args ◁ᵥ fp_atys ∗ fp_Pa → ∃ y : fp_rtype, ret ◁ᵥ fr_rty ∗ fr_R
 *)
  Record fn_params := FP {
    (* types of arguments (rc::args) *)
    fp_atys : list type;
    (* precondition (rc::requires) *)
    fp_Pa : iProp Σ;
    (* type of the existential quantifier (rc::exists) *)
    fp_rtype : Type;
    (* return type and postcondition (rc::returns and rc::ensures) *)
    fp_fr: fp_rtype → fn_ret;
  }.

  Definition fn_ret_prop {B} fn (fr : B → fn_ret) : option val → type → assert  :=
    (λ v ty, ⎡opt_ty_own_val (fn_return fn) ty v⎤ -∗ (<affine> ⌜match v with Some v => tc_val (fn_return fn) v | None => fn_return fn = Tvoid end⌝ ∗
       ∃ x, ⎡opt_ty_own_val (fn_return fn) (fr x).(fr_rty) v⎤ ∗ ⎡(fr x).(fr_R)⎤ ∗
       ∃ lv, stackframe_of1' cenv_cs fn lv))%I.

  Definition fn_ret_assert {B} fn (fr : B → fn_ret) : type_ret_assert :=
   {| T_normal := fn_ret_prop fn fr None tytrue;
      T_break := False;
      T_continue := False;
      T_return := fn_ret_prop fn fr |}.

  Definition FP_wf {B} (atys : list type) Pa (fr : B → fn_ret)  :=
    FP atys Pa B fr.

  Context (Espec : ext_spec OK_ty) (ge : Genv.t Clight.fundef Ctypes.type).

  (* Do we need a ty_own_temp, ty_own_var, etc. as well? *)
  Definition typed_var_block (idt: ident * Ctypes.type): assert :=
  ⌜(Ctypes.sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  ∃ b, lvar (fst idt) (snd idt) b ∗ ⎡(b, Ptrofs.zero) ◁ₗ uninit (snd idt)⎤.

  Definition typed_stackframe (f: Clight.function) (lv: list val) : assert :=
    ([∗ list] idt ∈ fn_vars f, typed_var_block idt) ∗
    ([∗ list] idt;v ∈ (Clight.fn_params f ++ fn_temps f);lv, temp (fst idt) v).

  Definition typed_function (fn : function) (fp : A → fn_params) : iProp Σ :=
    (<affine> ∀ x, <affine> ⌜Forall2 (λ (ty : type) '(_, p), ty.(ty_has_op_type) p MCNone) (fp x).(fp_atys) (Clight.fn_params fn)⌝ ∗
      □ ∀ n (lsa : vec val (length (fp x).(fp_atys))),
         (([∗ list] v;'(cty,t)∈lsa;zip (map snd (Clight.fn_params fn)) (fp x).(fp_atys), v ◁ᵥₐₗ|cty| t) ∗
          typed_stackframe fn (lsa ++ repeat Vundef (length fn.(fn_temps))) n ∗
          (fp x).(fp_Pa)) -∗
          typed_stmt Espec ge (fn.(fn_body)) fn (fn_ret_assert fn (fp x).(fp_fr)) n
    )%I.

  Global Instance typed_function_persistent fn fp : Persistent (typed_function fn fp) := _.
  Global Instance typed_function_affine fn fp : Affine (typed_function fn fp) := _.

  (* up? *)
  Global Instance leibniz_val : Equiv val := equivL.

  Import EqNotations.
  Lemma typed_function_equiv fn1 fn2 (fp1 fp2 : A → _) :
    fn1 = fn2 →
    ((∀ x, Forall2 (λ ty '(_, p), ty_has_op_type ty p MCNone) (fp_atys (fp2 x)) (Clight.fn_params fn2)) →
    (* TODO: replace the following with an equivalence relation for fn_params? *)
    (∀ x, ∃ Heq : (fp1 x).(fp_rtype) = (fp2 x).(fp_rtype),
          (fp1 x).(fp_atys) ≡ (fp2 x).(fp_atys) ∧
          (fp1 x).(fp_Pa) ≡ (fp2 x).(fp_Pa) ∧
          (∀ y, ((fp1 x).(fp_fr) y).(fr_rty) ≡ ((fp2 x).(fp_fr) (rew [λ x : Type, x] Heq in y)).(fr_rty) ∧
                ((fp1 x).(fp_fr) y).(fr_R) ≡ ((fp2 x).(fp_fr) (rew [λ x : Type, x] Heq in y)).(fr_R))) →
    typed_function fn1 fp1 ⊢ typed_function fn2 fp2)%type.
  Proof.
    iIntros (-> Hly Hfn) "HT".
    rewrite /typed_function.
    iIntros "!>" (x). iDestruct ("HT" $! x) as ([Hlen Hall]%Forall2_same_length_lookup) "#HT".
    have [Heq [Hatys [HPa Hret]]] := Hfn x.
    iSplit; [done|].
    iIntros "!> %% (Ha & Hstack)". rewrite -HPa.
    have [|lsa' Hlsa]:= vec_cast _ lsa (length (fp_atys (fp1 x))). { by rewrite Hatys. }
    iApply monPred_in_entails; first iApply typed_stmt_mono; last iApply ("HT" $! _ lsa'); simpl; try done.
    - iIntros "HR Hty".
      iDestruct ("HR" with "Hty") as (? y) "[?[??]]".
      have [-> ->]:= Hret y.
      iSplit => //.
      iExists (rew [λ x : Type, x] Heq in y). iFrame.
    - iIntros (v ?) "HR Hty".
      iDestruct ("HR" with "Hty") as (? y) "[?[??]]".
      have [-> ->]:= Hret y.
      iSplit => //.
      iExists (rew [λ x : Type, x] Heq in y). iFrame.
    - iFrame. rewrite Hlsa; iFrame.
      iClear "HT"; iStopProof.
      apply bi.equiv_entails_1_1, big_sepL2_proper_2; [try done..|].
      { rewrite Hatys //. }
      intros ??????? Hy. inv Hy.
      move: Hatys => /list_equiv_lookup Hatys.
      intros (? & ? & -> & Hty2 & Haty2)%lookup_zip_with_Some (? & ? & -> & Hty1 & Haty1)%lookup_zip_with_Some.
      rewrite Hty2 in Hty1; inv Hty1.
      have := Hatys k. rewrite Haty1 Haty2=> /(Some_equiv_eq _ _)[?[? [? Heqv]]] [_ ?].
      by f_equiv.
  Qed.

  Lemma prove_typed_function P `{!Persistent P} `{!Affine P} fn fp :
    (forall x, Forall2 (λ (ty : type) '(_, p), ty.(ty_has_op_type) p MCNone) (fp x).(fp_atys) (Clight.fn_params fn) ∧
     forall (lsa : vec val (length (fp x).(fp_atys))), ⎡P⎤ -∗ (([∗ list] v;'(cty,t)∈lsa;zip (map snd (Clight.fn_params fn)) (fp x).(fp_atys), ⎡v ◁ᵥₐₗ|cty| t⎤) ∗
          typed_stackframe fn (lsa ++ repeat Vundef (length fn.(fn_temps))) ∗
          ⎡(fp x).(fp_Pa)⎤) -∗
          typed_stmt Espec ge (fn.(fn_body)) fn (fn_ret_assert fn (fp x).(fp_fr))) →
    P ⊢ typed_function fn fp.
  Proof.
    intros; iIntros "#P".
    rewrite /typed_function.
    iIntros "!>" (x).
    destruct (H x) as (? & Hty).
    iSplit => //.
    iIntros "!>" (n lsa) "H".
    specialize (Hty lsa); apply monPred_in_entails with (i := n) in Hty.
    rewrite monPred_at_emp in Hty.
    iPoseProof (Hty with "[//]") as "Hty"; monPred.unseal.
    iApply ("Hty" with "[//] P [//]").
    iDestruct "H" as "(H & $ & $)".
    rewrite monPred_at_big_sepL2.
    iApply (big_sepL2_mono with "H").
    intros ?? (?,?) ??; by rewrite -monpred.monPred_embed_unseal monPred_at_embed.
  Qed.
    
  Definition fntbl_entry f fn := let '(b, o) := f in o = Ptrofs.zero /\ Genv.find_def ge b = Some (Gfun (Internal fn)) /\
    (Forall (λ it : ident * Ctypes.type, complete_type cenv_cs it.2 = true) (fn_vars fn)
       ∧ list_norepet (map fst (Clight.fn_params fn) ++ map fst (fn_temps fn))
         ∧ list_norepet (map fst (fn_vars fn))
           ∧ var_sizes_ok cenv_cs (fn_vars fn)
             (* extra conditions to guarantee has_layout *)
             ∧ Forall (λ it, composite_compute.complete_legal_cosu_type it.2 = true) (fn_vars fn)
             ∧ Forall (λ it, align_mem.LegalAlignasFacts.LegalAlignasDefs.is_aligned cenv_cs ha_env_cs la_env_cs it.2 0 = true) (fn_vars fn)).

  Lemma fntbl_entry_inj : forall f fn1 fn2, fntbl_entry f fn1 → fntbl_entry f fn2 → fn1 = fn2.
  Proof.
    destruct f; intros ?? (_ & ? & _) (_ & ? & _); congruence.
  Qed.

  Program Definition function_ptr_type (fp : A → fn_params) (f : address) : type := {|
    ty_has_op_type ot mt := (∃ fn, fntbl_entry f fn /\ ot = tptr (type_of_function fn))%type;
    ty_own β l := (∃ fn, <affine> ⌜l `has_layout_loc` tptr (type_of_function fn)⌝ ∗ l ↦[β]|tptr (type_of_function fn)| adr2val f ∗ <affine> ⌜fntbl_entry f fn⌝ ∗ <affine> ▷ typed_function fn fp)%I;
    ty_own_val cty v := (∃ fn, <affine> ⌜cty = tptr (type_of_function fn) /\ repinject cty v = adr2val f⌝ ∗ <affine> ⌜fntbl_entry f fn⌝ ∗ <affine> ▷ typed_function fn fp)%I;
  |}.
  Next Obligation. iDestruct 1 as (fn) "[? [H [? ?]]]". iExists _. iFrame. by iApply (heap_mapsto_own_state_share with "H"). Qed.
  Next Obligation. iIntros (fp f ot mt l (? & ? & ->)). iDestruct 1 as (??) "(?&%&?)". eapply fntbl_entry_inj in H; eauto; subst; done. Qed.
  Next Obligation. iIntros (fp f ot mt v (? & ? & ->)). iDestruct 1 as (? (? & Hv)) "?". simpl in Hv; subst. iPureIntro; hnf; split; auto. Qed.
  Next Obligation. iIntros (fp f ot mt v (fn & Htbl & ->)). iDestruct 1 as (??) "(?&%&?)". eapply fntbl_entry_inj in Htbl; eauto; subst. iFrame; eauto. Qed.
  Next Obligation. iIntros (fp f ot mt v ? (? & Htbl & ->) ?) "?". iDestruct 1 as (? (Heq & ?)) "?". simpl in *; subst.
    rewrite Heq in H; rewrite (mapsto_tptr _ _ _ (type_of_function fn)); by iFrame. Qed.
(*   Next Obligation.
    iIntros (fp f v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[%fn [-> ?]]". iPureIntro. naive_solver.
  Qed. *)

  Definition function_ptr (fp : A → fn_params) : rtype _ :=
    RType (function_ptr_type fp).

  Global Program Instance copyable_function_ptr cty p fp : Copyable cty (p @ function_ptr fp).
  Next Obligation.
    iIntros (cty p fp E l ? (? & He & ->)). iDestruct 1 as (fn Hl) "(Hl&%He2&#?)".
    eapply fntbl_entry_inj in He as <-; last done.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "(_ & % & Hl)" => //.
     iFrame; iFrame "#". iModIntro. unfold has_layout_loc. do 3 iSplit => //.
     iIntros "?"; iExists _; iSplitR => //.
     iMod (inv_alloc with "[-]") as "$"; first by iFrame.
     iModIntro. by iSplit.
  Qed.

  Global Instance function_ptr_defined cty p fp : DefinedTy cty (p @ function_ptr fp).
  Proof.
    iIntros (?) "(% & (_ & %) & ?)".
    iPureIntro; intros ->; by destruct cty.
  Qed.

  Opaque simple_mapsto.memory_block.

  Lemma stackframe_of_typed : forall f lv
    (Hcomplete : Forall (λ it, composite_compute.complete_legal_cosu_type it.2 = true) (fn_vars f))
    (Halign : Forall (λ it, align_mem.LegalAlignasFacts.LegalAlignasDefs.is_aligned cenv_cs ha_env_cs la_env_cs it.2 0 = true) (fn_vars f)),
    stackframe_of0' cenv_cs f lv ⊢ typed_stackframe f lv.
  Proof.
    intros; rewrite /stackframe_of0' /typed_stackframe.
    iIntros "(H & $)".
    iApply (big_sepL_mono with "H"); intros ?? H%elem_of_list_lookup_2.
    rewrite !Forall_forall in Hcomplete Halign.
    specialize (Hcomplete _ H); specialize (Halign _ H).
    rewrite /var_block0 /typed_var_block.
    iIntros "(% & % & $ & H)"; iSplit; first done.
    rewrite simple_mapsto.memory_block_weaken uninit_memory_block //; iFrame.
    iPureIntro.
    split3; simpl; auto.
    change expr.sizeof with Ctypes.sizeof.
    rewrite Z.add_0_l; split3; first rep_lia; last done.
    apply la_env_cs_sound; auto.
  Qed.

  Transparent simple_mapsto.memory_block.

  Lemma type_call_fnptr l i v vl ctys `{!TCEq (length vl) (length ctys)} retty cc tys fp T :
    (⎡([∗ list] v;'(cty,ty)∈vl; zip ctys tys, v ◁ᵥₐₗ|cty| ty)⎤ -∗ ∃ x,
      ⎡([∗ list] v;'(cty,ty)∈vl; zip ctys (fp x).(fp_atys), v ◁ᵥₐₗ|cty| ty)⎤ ∗
      ⎡(fp x).(fp_Pa)⎤ ∗ ∀ v x',
      ⎡((fp x).(fp_fr) x').(fr_R)⎤ -∗
      set_temp_opt i v (⎡opt_ty_own_val retty ((fp x).(fp_fr) x').(fr_rty) v⎤ -∗
      T_normal T))
    ⊢ typed_call Espec ge i v ⎡v ◁ᵥₐₗ|tptr (Tfunction ctys retty cc)| l @ function_ptr fp⎤ vl ctys retty cc tys T.
  Proof.
    inversion TCEq0 as [Hlen].
    iIntros "HT (%fn&(%&%)&%He&Hfn)".
    simpl in *; subst.
    inv H.
    rewrite /type_of_params map_length in Hlen.
    iExists (Internal fn); iSplit.
    { iPureIntro; destruct l, He as (-> & ? & ?); rewrite /adr2val /=; eexists; split3; eauto.
      { rewrite Genv.find_funct_ptr_iff //. }
      tauto. }
    iIntros "Htys !>"; iDestruct ("HT" with "Htys") as "(%x&Hvl&HPa&Hr)".
    iDestruct ("Hfn" $! x) as "[%Hl #Hfn]".
    iStopProof.
    split => n. repeat monPred.unseal.
    rewrite monPred_at_intuitionistically.
    iIntros "(Hfn & Hvl & HPa & Hpost) %% Hret %% Hstack !>".
    pose proof (Forall2_length Hl) as Hlena.
    rewrite Hlena -Hlen.
    iSpecialize ("Hfn" $! _ (Vector.of_list vl) with "[Hvl $HPa Hstack]").
    { destruct l, He as (_ & _ & _ & _ & _ & _ & ? & ?).
      rewrite vec_to_list_to_vec stackframe_of_typed //; iFrame. }
    iApply (monPred_in_entails with "[-]"); first apply wp_strong_mono.
    rewrite monPred_at_sep; iFrame "Hfn"; monPred.unseal.
    iSplit.
    - rewrite /fn_ret_prop /set_temp_opt /Clight_seplog.bind_ret; iIntros (??) "H !>"; monPred.unseal.
      unfold sqsubseteq in *; subst; iFrame.
      setoid_rewrite monPred_at_affinely.
      iDestruct ("H" with "[//] [//]") as (??) "(_ & HR & $)".
      iSplit; first done.
      iSpecialize ("Hpost" $! None with "[//] HR"); simpl.
      destruct i; simpl.
      * iDestruct "Hpost" as "($ & H)"; iIntros (? ->) "?"; by iApply ("H" with "[//] [$] [//]").
      * by iApply "Hpost".
    - do 2 (iSplit; intros; first by monPred.unseal; iIntros (??) "[]").
      rewrite /fn_ret_prop /set_temp_opt /Clight_seplog.bind_ret; iIntros (ret ? ->) "H !>"; monPred.unseal.
      iDestruct "H" as (?) "(? & H)".
      unfold sqsubseteq in *; subst; iFrame.
      setoid_rewrite monPred_at_affinely; iDestruct ("H" with "[//] [$]") as (??) "(Hretty & HR & $)".
      iSplit; first done.
      iSpecialize ("Hpost" $! ret with "[//] HR"); simpl.
      destruct i; simpl.
      * iDestruct "Hpost" as "($ & H)"; iIntros (? ->) "?"; by iApply ("H" with "[//] [$] [//]").
      * by iApply "Hpost".
  Qed.
  Definition type_call_fnptr_inst := [instance type_call_fnptr].
  Global Existing Instance type_call_fnptr_inst.

  Lemma subsume_fnptr_val_ex B v cty l1 l2 (fnty1 : A → fn_params) fnty2 `{!∀ x, ContainsEx (fnty2 x)} T:
    (∃ x, <affine> ⌜l1 = l2 x⌝ ∗ <affine> ⌜fnty1 = fnty2 x⌝ ∗ T x)
    ⊢ subsume (v ◁ᵥₐₗ|cty| l1 @ function_ptr fnty1) (λ x : B, v ◁ᵥₐₗ|cty| (l2 x) @ function_ptr (fnty2 x)) T.
  Proof. iIntros "H".
         iDestruct "H" as (x) "(% & (-> & ?))".
         rewrite /subsume.
         iIntros "H".
         iExists x. rewrite H0. iFrame.
  Qed.
  Definition subsume_fnptr_val_ex_inst := [instance subsume_fnptr_val_ex].
  Global Existing Instance subsume_fnptr_val_ex_inst | 5.

  (* TODO: split this in an ex and no_ex variant as for values *)
  Lemma subsume_fnptr_loc B l l1 l2  (fnty1 : A → fn_params) fnty2 T:
    (∃ x, <affine> ⌜l1 = l2 x⌝ ∗ <affine> ⌜fnty1 = fnty2 x⌝ ∗ T x)
      ⊢ subsume (l ◁ₗ l1 @ function_ptr fnty1) (λ x : B, l ◁ₗ (l2 x)  @ function_ptr (fnty2 x))  T .
  Proof.
    iIntros "H". iDestruct "H" as (x) "(% & (% & ?))".
    iIntros "H". iExists x. rewrite H0 H. iFrame.
  Qed.
  Definition subsume_fnptr_loc_inst := [instance subsume_fnptr_loc].
  Global Existing Instance subsume_fnptr_loc_inst | 5.
End function.
Arguments fn_ret_prop _ _ _ _ /.

(* We need to start a new section since the following rules use multiple different A. *)
Section function_extra.
  Context `{!typeG OK_ty Σ}.
 
  (*
  Lemma subsume_fnptr_no_ex A A1 A2 v l1 l2 (fnty1 : A1 → fn_params) (fnty2 : A2 → fn_params)
    `{!Inhabited A1} T:
    subsume (v ◁ᵥ l1 @ function_ptr fnty1) (λ x : A, v ◁ᵥ (l2 x) @ function_ptr fnty2) T :-
      and:
      | drop_spatial;
        ∀ a2,
        (* We need to use an implication here since we don't have
        access to the layouts of the function otherwise. If this is a
        problem, we could also add the argument layouts as part of the
        function pointer type. *)
        exhale ⌜Forall2 (λ ty1 ty2,
                    ∀ p, ty1.(ty_has_op_type) (UntypedOp p) MCNone →
                         ty2.(ty_has_op_type) (UntypedOp p) MCNone)
                  (fnty1 (inhabitant)).(fp_atys) (fnty2 a2).(fp_atys)⌝;
        inhale (fp_Pa (fnty2 a2));
        ls ← iterate: fp_atys (fnty2 a2) with [] {{ ty T ls,
               ∀ l, inhale (l ◁ₗ ty); return T (ls ++ [l]) }};
        ∃ a1,
        exhale ⌜length (fp_atys (fnty1 a1)) = length (fp_atys (fnty2 a2))⌝%I;
        iterate: zip ls (fp_atys (fnty1 a1)) {{ e T, exhale (e.1 ◁ₗ e.2); return T }};
        exhale (fp_Pa (fnty1 a1));
        ∀ ret1 ret_val,
        inhale (ret_val ◁ᵥ fr_rty (fp_fr (fnty1 a1) ret1));
        inhale (fr_R (fp_fr (fnty1 a1) ret1));
        ∃ ret2,
        exhale (ret_val ◁ᵥ fr_rty (fp_fr (fnty2 a2) ret2));
        exhale (fr_R (fp_fr (fnty2 a2) ret2)); done
      | ∃ x, exhale ⌜l1 = l2 x⌝; return T x.
  Proof.
    iIntros "(#Hsub & (%x & -> & HT))".
    iIntros "(%fn & -> & #Hfn & #Htyp_f1)".
    iExists x; iFrame. unfold function_ptr; simpl_type.
    iExists fn; iSplit => //; iFrame "#"; iNext.
    rewrite /typed_function. iIntros (a2).
    iDestruct ("Htyp_f1" $! inhabitant) as "(%Hlayouts1 & _)".
    iDestruct ("Hsub" $! a2) as "{Hsub} (%Hlayouts2 & Hsub)".
    iSplit; [iPureIntro|iModIntro].
    { move: Hlayouts1 Hlayouts2 => /Forall2_same_length_lookup[Hlen1 Hlookup1] /Forall2_same_length_lookup[Hlen2 Hlookup2] .
      apply Forall2_same_length_lookup. split; [lia|].
      move => i ty [name ly] ? Hlookup.
      have Hlen := lookup_lt_Some _ _ _ Hlookup.
      move: Hlen; rewrite -Hlen1 => /(lookup_lt_is_Some_2 _ _)[ty' Hty'].
      apply: Hlookup2  => //.
      by apply (Hlookup1 i _ (name, ly)).
    }
    iIntros (lsa lsv) "(Hargs & Hlocals & HP)".
    iSpecialize ("Hsub" with "HP").
    pose (INV := (λ i ls', ⌜ls' = take i lsa⌝ ∗
      [∗ list] l;t ∈ drop i lsa;drop i (fp_atys (fnty2 a2)), l ◁ₗ t)%I).
    iDestruct (iterate_elim1 INV with "Hsub [Hargs] [#]") as (ls') "((-> & ?) & (%a1 & %Hlen & Hsub))"; unfold INV; clear INV.
    { rewrite take_0 !drop_0. by iFrame. }
    { iIntros "!>" (i x2 ? ls' ?). iIntros "[-> Hinv] HT".
      have [|??]:= lookup_lt_is_Some_2 lsa i. {
        rewrite vec_to_list_length. by apply: lookup_lt_Some. }
      erewrite drop_S; [|done]. erewrite (drop_S _ _ i); [|done] => /=.
      iDestruct "Hinv" as "[Hl $]". iDestruct ("HT" with "[$]") as "HT". iExists _. iFrame.
      by erewrite take_S_r.
    }
    pose (INV := (λ i,
      [∗ list] l;t ∈ take i lsa;take i (fp_atys (fnty1 a1)), l ◁ₗ t)%I).
    iDestruct (iterate_elim0 INV with "Hsub [] [#]") as "[Hinv [Hpre1 Hsub]]"; unfold INV; clear INV.
    { by rewrite !take_0. } {
      iIntros "!>" (i ? ? (?&?&?&Hvs&?)%lookup_zip_with_Some); simplify_eq/=.
      iIntros "Hinv [? $]". rewrite lookup_take in Hvs.
      2: { rewrite -Hlen. by apply: lookup_lt_Some. }
      erewrite take_S_r; [|done]. erewrite take_S_r; [|done].
      rewrite big_sepL2_snoc. iFrame.
    }
    rewrite -Hlen in lsa *.
    iDestruct ("Htyp_f1" $! a1) as "{Htyp_f1} (_ & #Htyp_f1)".
    iSpecialize ("Htyp_f1" $! lsa lsv).
    rewrite !zip_with_length !take_ge ?vec_to_list_length; [|lia..].
    iSpecialize ("Htyp_f1" with "[$]").
    iApply (introduce_typed_stmt_wand with "Htyp_f1").
    iIntros (v ty) "Hret1 Hty" => /=.
    iDestruct ("Hret1" with "Hty") as "(%ret1 & Hty1 & Hpost1 & _)".
    iDestruct ("Hsub" $! ret1 v with "Hty1 Hpost1") as "(%ret2 & Hty2 & Hpost2 & _)".
    iExists ret2; iFrame.
  Qed.
  Definition subsume_fnptr_no_ex_inst := [instance subsume_fnptr_no_ex].
  Global Existing Instance subsume_fnptr_no_ex_inst | 10.
*)
End function_extra.

Notation "'fn(∀' x ':' A ';' T1 ',' .. ',' TN ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((fun x => FP_wf (B:=B) (@cons type T1%I .. (@cons type TN%I (@nil type)) ..) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  T1 ','  .. ','  TN ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.

Notation "'fn(∀' x ':' A ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((λ x, FP_wf (B:=B) (@nil type) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.

(*
Global Typeclasses Opaque typed_function.
Global Typeclasses Opaque function_ptr_type function_ptr.
*)

Section inline_function.
  Context `{!typeG OK_ty Σ} {cs : compspecs} (ge : Genv.t Clight.fundef Ctypes.type).

  Program Definition inline_function_ptr_type (fn : function) (f : address) : type := {|
    ty_has_op_type ot mt := (∃ t, ot = tptr t)%type;
    ty_own β l := (<affine> ⌜l `has_layout_loc` tptr tvoid⌝ ∗
                              l ↦[β]|tptr tvoid| (adr2val f) ∗ <affine> ⌜fntbl_entry ge f fn⌝)%I;
    ty_own_val cty v := (<affine> ⌜repinject cty v = adr2val f⌝ ∗ <affine> ⌜fntbl_entry ge f fn⌝)%I;
  |}.
  Next Obligation. iDestruct 1 as "[% [H ?]]". iFrame.
                   iMod (heap_mapsto_own_state_share with "H") as "$". done. Qed.
  Next Obligation. iIntros (fn f ot mt l ?). destruct H as (t & ->).
                   rewrite singleton.has_layout_loc_tptr.
                   by iDestruct 1 as "(% & ?)". Qed.
  Next Obligation. iIntros (fn f ot mt l ?). destruct H as (t & ->).
                   simpl; iDestruct 1 as "(-> & _)". iPureIntro; rewrite has_layout_val_by_value //=; intros ?; simpl.
                   rewrite andb_false_r //. Qed.
  Next Obligation. iIntros (fn f ot mt v ?). destruct H as (t & ->).
                   iIntros "(% & (? & ?))".
                   iExists (repinject (tptr t) f).
                   rewrite /heap_mapsto_own_state (mapsto_tptr _ _ _ t). by iFrame. Qed.
  Next Obligation. iIntros (fn f ot mt l v ? ?) "? (% & ?)". destruct H as (t & ->).
                   rewrite -has_layout_loc_tptr /heap_mapsto_own_state (mapsto_tptr _ _ _ tvoid). simpl in *; subst; by iFrame. Qed.

  Definition inline_function_ptr (fn : function) : rtype _ :=
    RType (inline_function_ptr_type fn).

  Global Program Instance copyable_inline_function_ptr cty p fn : Copyable (tptr cty) (p @ inline_function_ptr fn).
  Next Obligation.
    iIntros (? p fn E l ?). iDestruct 1 as "(%&Hl&%)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[% [% Hl]]" => //.
    rewrite (mapsto_tptr _ _ _ cty); iFrame. iModIntro. rewrite has_layout_loc_tptr. do 3 iSplit => //.
    rewrite (mapsto_tptr _ _ _ tvoid).
    iIntros "Hl"; iMod (heap_mapsto_own_state_from_mt with "Hl") as "$"; auto.
  Qed.

  Global Instance inline_function_ptr_defined p fn : DefinedTy (tptr tvoid) (p @ inline_function_ptr fn).
  Proof.
    iIntros (?) "(% & %)".
    by destruct v.
  Qed.

(*  Lemma type_call_inline_fnptr l v vl tys fn T:
    (⌜Forall2 (λ ty '(_, p), ty.(ty_has_op_type) (UntypedOp p) MCNone) tys (f_args fn)⌝ ∗
      foldr (λ '(v, ty) T lsa, ∀ l, l ◁ₗ ty -∗ T (lsa ++ [l]))
      (λ lsa, foldr (λ ly T lsv, ∀ l, l ◁ₗ uninit ly -∗ T (lsv ++ [l]))
                    (λ lsv,
                     introduce_typed_stmt fn (lsa ++ lsv) T)
                    fn.(f_local_vars).*2 [])
      (zip vl tys)
      [])
    ⊢ typed_call v (v ◁ᵥ l @ inline_function_ptr fn) vl tys T.
  Proof.
    iIntros "[%Hl HT] (->&Hfn) Htys" (Φ) "HΦ".
    iAssert ⌜Forall2 has_layout_val vl (f_args fn).*2⌝%I as %Hall. {
      iClear "Hfn HT HΦ".
      iInduction (fn.(f_args)) as [|[??]] "IH" forall (vl tys Hl).
      { move: Hl => /Forall2_nil_inv_r ->. destruct vl => //=. }
      move: Hl. intros (?&?&Heq&?&->)%Forall2_cons_inv_r.
      destruct vl => //=. iDestruct "Htys" as "[Hv Hvl]".
      iDestruct ("IH" with "[//] Hvl") as %?.
      iDestruct (ty_size_eq with "Hv") as %?; [done|].
      iPureIntro. constructor => //.
    }
    iApply (wp_call with "Hfn") => //. { by apply val_to_of_loc. }
    iIntros "!#" (lsa lsv Hly) "Ha Hv".
    iAssert ⌜length lsa = length (f_args fn)⌝%I as %Hlen1. {
      iDestruct (big_sepL2_length with "Ha") as %->.
      iPureIntro. move: Hall => /Forall2_length ->. by rewrite fmap_length.
    }
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    move: Hl Hall Hly. move: {1 2 3}(f_args fn) => alys Hl Hall Hly.
    have : lsa = [] ++ lsa by done.
    move: {1 5}([]) => lsr.
    move: {1 3 4}(lsa) Hly => lsa' Hly Hr.
    iInduction vl as [|v vl] "IH" forall (tys lsa' alys lsr Hr Hly Hl Hall) => /=. 2: {
       iDestruct (big_sepL2_cons_inv_r with "Ha") as (???) "[Hmt ?]".
       iDestruct (big_sepL2_cons_inv_l with "Htys") as (???) "[Hv' ?]". simplify_eq/=.
       move: Hl => /(Forall2_cons_inv_l _ _ _ _)[[??][?[?[??]]]]. simplify_eq/=.
       move: Hly => /(Forall2_cons _ _ _ _)[??].
       move: Hall => /(Forall2_cons _ _ _ _)[??].
       iDestruct (ty_ref with "[] Hmt Hv'") as "Hl"; [done..|].
       iSpecialize ("HT" with "Hl").
       iApply ("IH" with "[%] [//] [//] [//] HT [$] [$] [$] [$]").
       by rewrite -app_assoc/=.
    }
    iDestruct (big_sepL2_nil_inv_r with "Ha") as %?. subst.
    move: {1 2}(f_local_vars fn) => vlys.
    have : lsv = [] ++ lsv by done.
    move: {1 3}([]) => lvr.
    move: {2 3}(lsv) => lsv' Hr.
    iInduction lsv' as [|lv lsv'] "IH" forall (vlys lvr Hr) => /=. 2: {
       iDestruct (big_sepL2_cons_inv_l with "Hv") as (???) "[(%x&%&%&Hl) ?]". simplify_eq/=.
       iSpecialize ("HT" $! lv with "[Hl]"). { iExists _. iFrame. iPureIntro. split_and! => //. by apply: Forall_true. }
       iApply ("IH" with "[%] HT [$] [$] [$] [$]").
       by rewrite -app_assoc/=.
    }
    iDestruct (big_sepL2_nil_inv_l with "Hv") as %?. subst.
    simplify_eq/=.
    rewrite /introduce_typed_stmt !right_id_L.
    iExists _. iSplitR "HΦ" => /=.
    - iFrame. iApply ("HT" with "[-]"). iPureIntro. rewrite !app_length -Hlen1 -Hlen2 !app_length/=. lia.
    - iIntros (v). iDestruct 1 as (x') "[Hv [Hls HPr]]".
      iDestruct (big_sepL2_app_inv with "Hls") as "[$ $]".
      { left. by rewrite -Hlen1 right_id_L.  }
      by iApply ("HΦ" with "Hv HPr").
  Qed.
  Definition type_call_inline_fnptr_inst := [instance type_call_inline_fnptr].
  Global Existing Instance type_call_inline_fnptr_inst.*)
End inline_function.

Global Typeclasses Opaque inline_function_ptr_type inline_function_ptr.

(*** Tests *)
Section test.
  Context  `{!typeG OK_ty Σ} {cs : compspecs}.

  Local Definition test_fn := fn(∀ () : (); (uninit size_t); True) → ∃ () : (), void; True.
  Local Definition test_fn2 := fn(∀ () : (); True) → ∃ () : (), void; True.
  Local Definition test_fn3 := fn(∀ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z; uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t; True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True) → ∃ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z, uninit size_t; True%I.

  Goal ∀ Espec ge cty (l : address) fn, l ◁ᵥₐₗ|cty| l @ function_ptr Espec ge test_fn2 -∗ typed_function Espec ge fn test_fn.
  Abort.
End test.
