From VST.veric Require Import env Clight_core Clight_seplog.
From VST.typing Require Export type.
From VST.typing Require Import programs bytes.
From VST.typing Require Import type_options.

Section function.
  Context `{!typeG OK_ty Σ} {cs : compspecs} {A : TypeTree}. (* should we fix this to ConstType? *)
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

  Definition opt_ty_own_val cty t o :=
    match o with Some v => v ◁ᵥₐₗ|cty| t | None => emp end.

  Global Instance opt_ty_own_val_proper cty : Proper (equiv ==> eq ==> equiv) (opt_ty_own_val cty).
  Proof. intros ??? [|] ??; subst; simpl; by rewrite ?H. Qed.

  Definition fn_ret_prop {B} fn (fr : B → fn_ret) : option val → type → assert :=
    (λ v ty, <affine> ⌜match v with Some v => tc_val (fn_return fn) v | None => fn_return fn = Tvoid end⌝ ∗
     (⎡opt_ty_own_val (fn_return fn) ty v⎤ -∗ ∃ x, ⎡opt_ty_own_val (fn_return fn) (fr x).(fr_rty) v⎤ ∗ ⎡(fr x).(fr_R)⎤ ∗
      ∃ lv, stackframe_of' cenv_cs fn lv))%I.

  Definition FP_wf {B} (atys : list type) Pa (fr : B → fn_ret)  :=
    FP atys Pa B fr.

  Context (Espec : ext_spec OK_ty) (ge : Genv.t Clight.fundef Ctypes.type).

  (* Do we need a ty_own_temp, ty_own_var, etc. as well? *)
  Definition typed_var_block (idt: ident * Ctypes.type): assert :=
  ⌜(Ctypes.sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  ∃ b, lvar (fst idt) (snd idt) b ∗ ⎡(b, 0) ◁ₗ uninit (snd idt)⎤.

  Definition typed_stackframe (f: Clight.function) (lv: list val) : assert :=
    ([∗ list] idt ∈ fn_vars f, typed_var_block idt) ∗
    ([∗ list] idt;v ∈ (Clight.fn_params f ++ fn_temps f);lv, temp (fst idt) v).

  Definition typed_function (fn : function) (fp : @dtfr Σ A → fn_params) : iProp Σ :=
    (<affine> ∀ x, <affine> ⌜Forall2 (λ (ty : type) '(_, p), ty.(ty_has_op_type) p MCNone) (fp x).(fp_atys) (Clight.fn_params fn)⌝ ∗
      □ ∀ n (lsa : vec val (length (fp x).(fp_atys))),
         (([∗ list] v;'(cty,t)∈lsa;zip (map snd (Clight.fn_params fn)) (fp x).(fp_atys), v ◁ᵥₐₗ|cty| t) ∗
          typed_stackframe fn (lsa ++ repeat Vundef (length fn.(fn_temps))) n ∗
          (fp x).(fp_Pa)) -∗
          typed_stmt Espec ge (fn.(fn_body)) fn (fn_ret_prop fn (fp x).(fp_fr)) n
    )%I.

  Global Instance typed_function_persistent fn fp : Persistent (typed_function fn fp) := _.
  Global Instance typed_function_affine fn fp : Affine (typed_function fn fp) := _.

  (* up? *)
  Global Instance leibniz_val : Equiv val := equivL.

  Import EqNotations.
  Lemma typed_function_equiv fn1 fn2 (fp1 fp2 : @dtfr Σ A → _) :
    fn1 = fn2 →
    ((∀ x, Forall2 (λ ty '(_, p), ty_has_op_type ty p MCNone) (fp_atys (fp2 x)) (Clight.fn_params fn2)) →
    (* TODO: replace the following with an equivalenve relation for fn_params? *)
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
    iApply monPred_in_entails; first iApply typed_stmt_mono; last iApply ("HT" $! _ lsa').
    - iIntros (v ?) "($ & HR) Hty".
      iDestruct ("HR" with "Hty") as (y) "[?[??]]".
      have [-> ->]:= Hret y.
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

  Definition fntbl_entry f fn := let '(b, o) := f in o = 0 /\ Genv.find_def ge b = Some (Gfun (Internal fn)).

  Lemma fntbl_entry_inj : forall f fn1 fn2, fntbl_entry f fn1 → fntbl_entry f fn2 → fn1 = fn2.
  Proof.
    destruct f; intros ?? (_ & ?) (_ & ?); congruence.
  Qed.

  Program Definition function_ptr_type (fp : dtfr A → fn_params) (f : address) : type := {|
    ty_has_op_type ot mt := (∃ fn, fntbl_entry f fn /\ ot = tptr (type_of_function fn))%type;
    ty_own β l := (∃ fn, <affine> ⌜l `has_layout_loc` (tptr tvoid)⌝ ∗ l ↦[β]|tptr tvoid| adr2val f ∗ <affine> ⌜fntbl_entry f fn⌝ ∗ ▷ typed_function fn fp)%I;
    ty_own_val cty v := (∃ fn, <affine> ⌜cty = tptr (type_of_function fn) /\ repinject cty v = adr2val f⌝ ∗ <affine> ⌜fntbl_entry f fn⌝ ∗ ▷ typed_function fn fp)%I;
  |}.
  Next Obligation. iDestruct 1 as (fn) "[? [H [? ?]]]". iExists _. iFrame. by iApply (heap_mapsto_own_state_share with "H"). Qed.
  Next Obligation. iIntros (fp f ot mt l (? & ? & ->)). rewrite singleton.has_layout_loc_tptr. by iDestruct 1 as (??) "?". Qed.
  Next Obligation. iIntros (fp f ot mt v (? & ? & ->)). iDestruct 1 as (? (? & Hv)) "?". simpl in Hv; subst. iPureIntro; hnf; split; auto.
    intros ?; done. Qed.
  Next Obligation. iIntros (fp f ot mt v (fn & Htbl & ->)). iDestruct 1 as (??) "(?&%&?)". eapply fntbl_entry_inj in Htbl; eauto; subst.
    rewrite /heap_mapsto_own_state (singleton.mapsto_tptr _ _ _ (type_of_function fn)); iFrame; eauto. Qed.
  Next Obligation. iIntros (fp f ot mt v ? (? & Htbl & ->) ?) "?". iDestruct 1 as (? (? & ?)) "?"; simpl in *; subst.
    rewrite singleton.has_layout_loc_tptr in H. rewrite /heap_mapsto_own_state (singleton.mapsto_tptr _ _ _ tvoid); by iFrame. Qed.
(*   Next Obligation.
    iIntros (fp f v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[%fn [-> ?]]". iPureIntro. naive_solver.
  Qed. *)

  Definition function_ptr (fp : dtfr A → fn_params) : rtype _ :=
    RType (function_ptr_type fp).

(*   Global Program Instance copyable_function_ptr p fp : Copyable (p @ function_ptr fp).
  Next Obligation.
    (* might not be true because of ▷ *)
  Admitted.
  Next Obligation.
    iIntros (p fp E ly l ? (? & ->)). iDestruct 1 as (fn Hl) "(Hl&?&?)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    erewrite singleton.mapsto_tptr. iFrame. iModIntro. unfold has_layout_loc. rewrite singleton.field_compatible_tptr. do 2 iSplit => //. by iIntros "_".
  Qed. *)

(*   (* up *)
  Lemma monPred_at_big_sepL2 {BI : bi} {I : biIndex} {B C} i (Φ : nat → B → C → monPred I BI) l m :
    ([∗ list] k↦x;y ∈ l;m, Φ k x y) i ⊣⊢ [∗ list] k↦x;y ∈ l;m, Φ k x y i.
  Proof. rewrite !big_sepL2_alt. monPred.unseal; rewrite monPred_at_big_sepL //. Qed. *)

  Lemma stackframe_of_typed : forall f lv, stackframe_of' cenv_cs f lv ⊢ typed_stackframe f lv.
  Proof.
  Admitted.

  Lemma type_call_fnptr f l i e el fp tys T:
    match typeof e with Tfunction ctl retty cc =>
    (typed_exprs ge f el ctl (λ vl tl, ⌜tl = tys⌝ ∧ ∃ x,
      ([∗ list] v;'(cty,ty)∈vl;zip ctl (fp x).(fp_atys), ⎡v ◁ᵥₐₗ|cty| ty⎤) ∗
      ⎡(fp x).(fp_Pa)⎤ ∗ ∀ v x',
      ⎡((fp x).(fp_fr) x').(fr_R)⎤ -∗
      set_temp_opt i v (⎡opt_ty_own_val retty ((fp x).(fp_fr) x').(fr_rty) v⎤ -∗
        T None tytrue)))
    | _ => False end
    ⊢ typed_call Espec ge f i e (typed_val_expr ge f e (λ v _, ⎡v ◁ᵥ|tptr tvoid| l @ function_ptr fp⎤)) el tys T.
  Proof.
    rewrite /typed_exprs /typed_call.
    destruct (typeof e) eqn: Hargty; try by iIntros "[]".
    iIntros "HT He".
    iApply wp_call; iApply "He".
    iIntros (??) "Hty Hfp".
    iDestruct "Hfp" as (? (_ & H) Htbl) "Hfp"; simpl in H; subst.
    assert (typeof e = type_of_function fn) as Hsig.
    { admit. (* e evaluates to a pointer to fn, but is that enough to guarantee that it was declared as tptr fn? *) }
    rewrite Hargty in Hsig; inv Hsig.
    iExists (map snd (Clight.fn_params fn)), (fn_return fn), (fn_callconv fn); iSplit.
    { rewrite Hargty //. }
    iApply "HT".
    iIntros (??) "Hvl (-> & Hpre) %Hlen".
    iDestruct "Hpre" as (x) "(Hargs & Hpre & Hret)".
    iExists (Internal fn); iSplit.
    { iPureIntro.
      destruct l, Htbl as (-> & ?).
      rewrite -Genv.find_funct_ptr_iff in H.
      exists b; split3; auto; split; auto; simpl.
      admit. (* wf conditions *) }
    iNext; rewrite /= /internal_call_assert.
    iStopProof.
    split => n; monPred.unseal.
    rewrite !monPred_at_big_sepL2.
    iIntros "(Hl & Hf & Htys & Hatys & HP & Hpost) %% Hret %% Hstack !>".
    rewrite /typed_function.
    iSpecialize ("Hf" $! x).
    iDestruct "Hf" as "(%Hop & #Hf)".
    pose proof (Forall2_length Hop) as Hlena.
    rewrite map_length in Hlen; rewrite Hlena -Hlen.
    iPoseProof ("Hf" $! _ (Vector.of_list vl) with "[Hatys Hstack $HP]") as "Hbody"; iClear "Hf".
    { rewrite vec_to_list_to_vec.
      iSplitL "Hatys".
      - iApply (big_sepL2_mono with "Hatys").
        intros ?? (?, ?); done.
      - iStopProof; apply monPred_in_entails, stackframe_of_typed. }
    iApply (monPred_in_entails with "[-]"); first apply wp_strong_mono.
    rewrite monPred_at_sep; iFrame "Hbody"; monPred.unseal.
    iSplit.
    - rewrite /fn_ret_prop /set_temp_opt /Clight_seplog.bind_ret; iIntros (??) "H !>"; monPred.unseal.
      rewrite monPred_at_affinely; iDestruct "H" as "(% & H)".
      unfold sqsubseteq in *; subst; iFrame.
      iDestruct ("H" with "[//] [//]") as (?) "(_ & HR & ?)".
      iSplitL "Hpost HR".
      + iSplit; first done.
        iSpecialize ("Hpost" $! None with "[//] HR"); simpl.
        destruct i; simpl.
        * iDestruct "Hpost" as "($ & H)"; iIntros (? ->) "?"; by iApply ("H" with "[//] [$] [//]").
        * by iApply "Hpost".
      + iFrame. admit.
    - do 2 (iSplit; intros; first by monPred.unseal; iIntros (??) "[]").
      rewrite /fn_ret_prop /set_temp_opt /Clight_seplog.bind_ret; iIntros (ret ? ->) "H !>"; monPred.unseal.
      setoid_rewrite monPred_at_affinely; iDestruct "H" as (?) "(? & %Htc & H)".
      unfold sqsubseteq in *; subst; iFrame.
      iDestruct ("H" with "[//] [$]") as (?) "(Hretty & HR & ?)".
      iSplitL "Hpost HR Hretty".
      + destruct ret; last by apply tc_val_Vundef in Htc.
        iSplit; first done.
        iSpecialize ("Hpost" $! (Some v) with "[//] HR"); simpl.
        destruct i; simpl.
        * iDestruct "Hpost" as "($ & H)"; iIntros (? ->) "?"; by iApply ("H" with "[//] [$] [//]").
        * by iApply "Hpost".
      + iFrame. admit.
  (*Qed.*) Admitted.
  Definition type_call_fnptr_inst := [instance type_call_fnptr].
(*  Global Existing Instance type_call_fnptr_inst. *)

  Lemma subsume_fnptr_val_ex B v l1 l2 (fnty1 : dtfr A → fn_params) fnty2 `{!∀ x, ContainsEx (fnty2 x)} T:
    (∃ x, <affine> ⌜l1 = l2 x⌝ ∗ <affine> ⌜fnty1 = fnty2 x⌝ ∗ T x)
    ⊢ subsume (v ◁ᵥ l1 @ function_ptr fnty1) (λ x : B, v ◁ᵥ (l2 x) @ function_ptr (fnty2 x)) T.
  Proof. iIntros "H".
         iDestruct "H" as (x) "(% & (-> & ?))".
         rewrite /subsume.
         iIntros "H".
         iExists x. rewrite H0. iFrame.
  Qed.
  Definition subsume_fnptr_val_ex_inst := [instance subsume_fnptr_val_ex].
  Global Existing Instance subsume_fnptr_val_ex_inst | 5.

  (* TODO: split this in an ex and no_ex variant as for values *)
  Lemma subsume_fnptr_loc B l l1 l2  (fnty1 : dtfr A → fn_params) fnty2 T:
    (∃ x, <affine> ⌜l1 = l2 x⌝ ∗ <affine> ⌜fnty1 = fnty2 x⌝ ∗ T x)
      ⊢ subsume (l ◁ₗ l1 @ function_ptr fnty1) (λ x : B, l ◁ₗ (l2 x)  @ function_ptr (fnty2 x))  T .
  Proof.
    iIntros "H". iDestruct "H" as (x) "(% & (% & ?))".
    iIntros "H". iExists x. rewrite H0 H. iFrame.
  Qed.
  Definition subsume_fnptr_loc_inst := [instance subsume_fnptr_loc].
  Global Existing Instance subsume_fnptr_loc_inst | 5.
End function.
Arguments fn_ret_prop _ _ _ /.

(* We need start a new section since the following rules use multiple different A. *)
Section function_extra.
  Context `{!typeG OK_ty Σ}.
 
  (*
  Lemma subsume_fnptr_no_ex A A1 A2 v l1 l2 (fnty1 : { A1 : TypeTree & (dtfr A1 → fn_params)%type}) (fnty2 : { A2 : TypeTree & (dtfr A2 → fn_params)%type})
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
  Context `{!typeG OK_ty Σ} {cs : compspecs}. 

  Program Definition inline_function_ptr_type (fn : funspec) (f : address) : type := {|
    ty_has_op_type ot mt := (∃ t, ot = tptr t)%type;
    ty_own β l := (<affine> ⌜field_compatible (tptr tvoid) [] l⌝ ∗
                              l ↦_(tptr tvoid)[β] (adr2val f) ∗ func_ptr fn f)%I;
    ty_own_val v := (<affine> ⌜v = adr2val f⌝ ∗ func_ptr fn f)%I;
  |}.
  Next Obligation. iDestruct 1 as "[% [H ?]]". iFrame.
                   iMod (heap_mapsto_own_state_share with "[$H]") as "H". iFrame "H". done. Qed.
  Next Obligation. iIntros (fn f ot mt l ?). destruct H as (t & ->).
                   rewrite /has_layout_loc singleton.field_compatible_tptr.
                   by iDestruct 1 as "(% & ?)". Qed.
  Next Obligation. iIntros (fn f ot mt l ?). destruct H as (t & ->).
                   iDestruct 1 as "(-> & _)". iPureIntro; intros ?; hnf; simple_if_tac; done. Qed.
  Next Obligation. iIntros (fn f ot mt v ?). destruct H as (t & ->).
                   iIntros "(% & (? & ?))".
                   iExists f.
                   rewrite /heap_mapsto_own_state. erewrite singleton.mapsto_tptr. by iFrame. Qed.
  Next Obligation. iIntros (fn f ot mt l v ? ?) "? (% & ?)". destruct H as (t & ->).
                   rewrite /heap_mapsto_own_state.
                   erewrite singleton.mapsto_tptr. rewrite <- H1. iFrame.
                   iPureIntro.
                   by rewrite <- singleton.field_compatible_tptr. Qed.

  Definition inline_function_ptr (fn : funspec) : rtype _ :=
    RType (inline_function_ptr_type fn).

  Global Program Instance copyable_inline_function_ptr p fn : Copyable (p @ inline_function_ptr fn).
  Next Obligation.
    iIntros (p fp E ly l ? (? & ->)). iDestruct 1 as "(%&Hl&?)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    erewrite singleton.mapsto_tptr. iFrame. iModIntro. rewrite /has_layout_loc singleton.field_compatible_tptr. do 2 iSplit => //. by iIntros "_".
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

  Goal ∀ Espec ge (l : address) fn, l ◁ᵥ l @ function_ptr(A := ConstType _) Espec ge test_fn2 -∗ typed_function(A := ConstType _) Espec ge fn test_fn.
  Abort.
End test.
