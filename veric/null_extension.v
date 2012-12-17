Load loadpath.
Require Import msl.base
               veric.sim veric.step_lemmas veric.base veric.expr veric.extspec
               veric.extension veric.extension_proof.

Set Implicit Arguments.

Section NullExtension.
 Variables
  (fT vT cT dT Z: Type) (** external states *)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT) 
  (csig: ext_sig mem Z) (** client signature *)
  (genv_mapT: forall i:nat, Genv.t fT vT)
  (init_world: Z)
  (at_external_handled: forall c ef args sig,
    at_external csemT c = Some (ef, sig, args) -> IN ef csig = true).

 Definition cores := fun _:nat => csemT.

 Local Open Scope nat_scope.

 Definition xT := cT.
 Definition proj_core (i: nat) (s: xT) := if eq_nat_dec i 0 then Some s else None.
 Definition active := fun _:xT => 0.
 Definition runnable := fun (s: xT) => 
   match at_external csemT s, safely_halted csemT s with 
     | None, None => true
     | _, _ => false
   end.
 Definition proj_zint := fun _:xT => tt.
 Definition proj_zext := fun z: Z => z.
 Definition zmult := fun (_:unit) (z: Z) => z.
 Definition handled: list AST.external_function := nil.

 Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.

 Obligation Tactic := 
   autounfold with null_unfold;
   intros; try solve [eexists; eauto|congruence].

 Definition fT' := fun i:nat => fT.
 Definition vT' := fun i:nat => vT.
 
 Program Definition null_extension := Extension.Make 
  (fun i:nat => Genv.t (fT' i) (vT' i))
  csemT cores csig csig handled
  proj_core _  
  active _ 
  runnable _ _ _ _  
  proj_zint proj_zext zmult _ _ _.
 Next Obligation.
   revert H0; case_eq (eq_nat_dec i 0).
   intros -> _; exists s; auto.
   congruence.
 Qed.
 Next Obligation.
   if_tac; exists s; auto.
   elimtype False; apply H; auto.
 Qed.
 Next Obligation. 
   if_tac in H0; try congruence; inv H0; inv H.
   unfold fT', vT' in *.
   destruct (at_external csemT c); try solve[congruence].
   destruct p as [[? ?] ?]. 
   right; eexists; eexists; eexists; eauto.
   destruct (safely_halted csemT c); try solve[congruence].
   solve[left; eexists; eauto].
 Qed.
 Next Obligation. inversion H; subst; eapply at_external_handled; eauto. Qed.
 Next Obligation. 
  inversion H; subst; if_tac in H; try congruence. 
  unfold fT', vT' in *.
  inversion H3; subst.
  solve[rewrite H0 in H1; congruence].
 Qed.
 Next Obligation. unfold linkable; intros; inv H0; inv H1; exists x'; auto. Qed.

End NullExtension.

Section NullExtensionSafe.
 Variables
  (fT vT cT dT Z: Type) (** external states *)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT) 
  (csig: ext_sig mem Z) (** client signature *)
  (genv_mapT: forall i:nat, Genv.t fT vT)
  (init_world: Z)
  (at_external_handled: forall c ef args sig,
    at_external csemT c = Some (ef, sig, args) -> IN ef csig = true)
  (ge: Genv.t fT vT).

 Import ExtensionSafety.

 Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.

 Obligation Tactic := 
   autounfold with null_unfold;
   intros; try solve [eexists; eauto|congruence].

 Lemma null_extension_safe (csem_fun: corestep_fun csemT): 
  safe_extension ge (fun _:nat => ge) (null_extension csemT csig at_external_handled).
 Proof.
 destruct (ExtensionSafety (null_extension csemT csig at_external_handled) 
  ge (fun _:nat => ge)) as [PF].
 apply PF.
 constructor; autounfold with null_unfold in *.

 (*1*) intros until m'; intros H1 H4 H5 H6. 
 assert (H3:True) by auto.
 unfold Extension.proj_core in H4; simpl in H4.
 generalize H4 as H4'; intro.
 unfold proj_core in H4; if_tac in H4; try solve[congruence].
 inversion H4 as [H7]; rewrite H7 in *; clear H7 H4.
 rewrite H in *; clear H.
 unfold Extension.proj_core; simpl; unfold proj_core.
 simpl in H5.
 f_equal; generalize (csem_fun _ _ _ _ _ _ _ H5 H6); inversion 1; auto.
 simpl in H1|-*.
 unfold proj_zint, all_safe in *.
 intros until c0; intros H0.
 assert (H8:True) by auto.
 inversion H0 as [H7]. simpl in H0. rewrite H7 in *; clear H0.
 unfold proj_core in H7.
 if_tac in H7; try solve[congruence].
 rewrite <-H0 in *; clear H; inversion H7 as [H].
 rewrite H in *; clear H7 H.
 solve[eapply safe_corestep_forward; eauto].

 (*2*) intros until c; intros H1 H3 H5.
 assert (H4:True) by auto.
 spec H1 (active s) c H5.
 simpl in H5.
 simpl in H3; unfold runnable in H3; simpl in H3.
 case_eq (at_external csemT s).
 intros [[ef sig] args] H6.
 rewrite H6 in H3.
 simpl in H5; unfold proj_core in H5; simpl in H5; inversion H5; subst.
 congruence.
 intros H6.
 rewrite H6 in H3.
 unfold proj_core in H5.
 if_tac in H5; try congruence.
 inv H5.
 case_eq (safely_halted csemT c); try congruence.
 intros rv Hsafe.
 rewrite Hsafe in H3.
 congruence.
 unfold fT', vT' in *.
 simpl in H1.
 rewrite H6 in H1.
 intros Hsafe; rewrite Hsafe in H1.
 destruct H1 as [c' [m' [H1 H7]]].
 solve[exists c'; exists c'; exists m'; split; auto].

 (*3*) intros until x; intros H2 H3 H4 H5 H6 H7 H8.
 assert (H1:True) by auto.
 apply ListSet.set_mem_correct1 in H4.
 unfold handled, ListSet.set_In in H4.
 solve[inversion H4].

 (*4*) intros until m; intros H1 H2 H3.
 simpl in H2; unfold runnable in H2.
 inversion H3; subst.
 unfold compose in H0;  simpl in H0.
 rewrite H0 in H2.
 case_eq (safely_halted csemT s); intros; try solve[congruence].
 rewrite H in H2.
 right; exists v; auto.
 solve[rewrite H in H2; congruence].

 (*5*) intros until rv; intros H2 H3 H4.
 unfold fT', vT' in *.
 simpl.
 apply corestep_not_halted in H4.
 simpl in H2; inversion H2; subst.
 unfold proj_core in H0.
 solve[if_tac in H0; try solve[congruence]].

 (*6*) intros until c; inversion 1; subst.
 intros H4 H5; intros until c0; intros H6; split.
 intros H8.
 assert (H7:True) by auto.
 simpl in H8; unfold proj_core in H8; simpl in H8; inversion H8; subst.
 simpl; unfold proj_core; simpl.
 simpl in H6; unfold active in H6.
 if_tac; auto.
 exfalso; apply H6; auto.
 intros n z z' H8.
 assert (H7:True) by auto.
 simpl in H8; unfold proj_core in H8; simpl in H8.
 simpl in H6; unfold active in H6; simpl in H6.
 if_tac in H8; auto.
 inversion H8; subst.
 exfalso; apply H6; auto.
 solve[congruence].

 (*7*) intros until args; intros H1.
 solve[exists s; split; auto].

 (*8*) intros until Q.
 unfold fT', vT' in *.
 intros H2 H3 H4 H5 H6.
 assert (H1:True) by auto.
 intros H12; simpl; exists c'; split3; auto.
 simpl in H2; unfold proj_core in H2.
 if_tac in H2; try solve[congruence].

 (*9*) intros until Q; intros H2 H3 H4 H5 H6 H7 H70 [H8 H9]; 
 intros until c0; intros H10; split.
 intros H12.
 assert (H11:True) by auto.
 simpl in H12; unfold proj_core in H12; simpl in H12.
 if_tac in H12; auto.
 simpl in H9; unfold proj_core in H9; simpl in H9.
 simpl in H10; unfold active in H10; simpl in H10.
 exfalso; apply H10; auto.
 congruence.
 intros ge'  n H12.
 simpl in H10, H12.
 unfold active in H10; unfold proj_core in H12.
 if_tac in H12.
 exfalso; auto.
 congruence.
 Qed.

End NullExtensionSafe.

(*
  (F V fS fT vS vT: Type) (** global environments *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (dS dT: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F V) cS mem dS) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F V) cT mem dT) (** extended target semantics *)
  (csemS: CoreSemantics (Genv.t fS vS) cS mem dS) 
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT) 
  (csig: ext_sig mem Z) (** client signature *)
  (esig: ext_sig mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variables 
  (ge: Genv.t F V) (geS: Genv.t fS vS) (geT: Genv.t fT vT).

 Variable (E_S: Extension.Sig (fun i => Genv.t ((fun _ => fS) i) ((fun _ => vS) i)) 
                  (fun _ => cS) Zint esemS (fun i:nat => Some ((fun _ => csemS) i)) 
                  csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t ((fun _ => fT) i) ((fun _ => vT) i)) 
                  (fun _ => cT) Zint esemT (fun i:nat => Some ((fun _ => csemT) i)) 
                  csig esig handled).

 Variable entry_points: list (val*val*signature).

 Import Sim_inj.

 Variable max_threads: nat.

 Variable core_simulations: forall i:nat, 
   Forward_simulation_inject dS dT csemS csemT geS geT entry_points.
*)
(*
Section NullExtensionCompilable.
 Variables 
  (F V fS vS fT vT cS cT dS dT Z: Type) 
  (csig: ext_sig mem Z)
  (init_world: Z)
  (entry_points: list (val*val*signature))
  (csemS: CoreSemantics (Genv.t fS vS) cS mem dS)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT)
  (at_external_handledS: forall c ef args sig,
    at_external csemS c = Some (ef, sig, args) -> IN ef csig = true)
  (at_external_handledT: forall c ef args sig,
    at_external csemT c = Some (ef, sig, args) -> IN ef csig = true).

 Variables (ge: Genv.t F V) (geS: Genv.t fS vS) (geT: Genv.t fT vT).

 Definition E_S: 
  Extension.Sig (fun i : nat => Genv.t ((fun _ => fS) i) ((fun _ => vS) i))
   (fun _ : nat => cS) unit csemS (fun _:nat => csemS) csig csig handled := 
  null_extension csemS csig at_external_handledS.
 Definition E_T: 
  Extension.Sig (fun i : nat => Genv.t ((fun _ => fT) i) ((fun _ => vT) i))
   (fun _ : nat => cT) unit csemT (fun _:nat => csemT) csig csig handled := 
 null_extension csemT csig at_external_handledT.

 Import Sim_inj.

 Variable core_simulations: forall i:nat,
  Forward_simulation_inject dS dT csemS csemT geS geT entry_points.

 Definition genv_mapS := fun i:nat => geS.
 Definition genv_mapT := fun i:nat => geT.
Set Printing All.
Check CompilableExtension.Sig.
 Lemma null_extension_compilable:
   @CompilableExtension.Sig F V cS cT 
    (fun _ => fS) (fun _ => fT) (fun _ => vS) (fun _ => vT) (fun _ => cS) (fun _ => cT)
    dS dT Z unit Z csemS csemT (fun _ => csemS) (fun _ => csemT)
    ge genv_mapS genv_mapT E_S E_T core_simulations.

End NullExtensionCompilable.
*)