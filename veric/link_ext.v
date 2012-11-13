Load loadpath.
Require Import compcert.AST.
Require Import veric.base.
Require Import veric.sim. 
Require Import List.

Inductive globdef (F V: Type) : Type :=
      | Gfun (f: F)
      | Gvar (v: globvar V).

Record Module (F V:Type) := mkmodule {
      fun_defs: list (ident * globdef F V);
      fun_def_unique: forall f gdef1 gdef2,
            In (f,gdef1) fun_defs -> In (f,gdef2) fun_defs -> gdef1=gdef2
    }.

Fixpoint lookup_ {F V} (l:list (ident * globdef F V)) f :=
   match l with nil => None
     | cons HD TL => match HD with (ff,dd) => if peq ff f then Some dd else lookup_ TL f end
   end.

Definition M_lookup {F V} (M:Module F V) (f:ident) : option (globdef F V) :=
  lookup_ (fun_defs _ _ M) f. 
    
Definition M_defines {F V} (M:Module F V) (f:ident): Prop :=
   exists gdef,  In (f,gdef) M.(fun_defs _ _ ).

Lemma M_defines_iff_M_lookup: forall F V (M:Module F V) f,
       M_defines M f <-> exists d, M_lookup M f = Some d.
  Proof. intros. unfold M_defines. unfold M_lookup. destruct M as [l U]. simpl in *. clear U.
     induction l; simpl; split; intros. 
         destruct H. contradiction.
         destruct H. inv H.
   destruct H.
       destruct H; subst. 
          exists x. apply peq_true.
      destruct a as [ff dd]. destruct IHl as [? _]. destruct H0. exists x; assumption.
          remember (peq ff f ) as b. destruct b. exists dd; trivial.
         exists x0. trivial.
  destruct H. destruct a as [ff dd].
       remember (peq ff f ) as b. destruct b. inv H.  exists x; left; trivial.
       destruct IHl as [_ ?]. destruct H0. exists x; assumption.
         exists x0. right. trivial.
Qed.
 
(*A pre-program is a nat-indexed finite collection of modules. The type of PP_find, together with the right-to-left implication
  of   PP_find_Some ensures that no identifier is defined by two modules below the watermark NumModules.*)
Record PreProgram := mkPreProgram {
    FParams: nat -> Type;
    VParams: nat -> Type;
    NumModules : nat;
    Modules: forall i,  (Module (FParams i) (VParams i));
    PP_find: ident -> option nat;
    PP_find_None: forall f, PP_find f = None <-> (forall n, (n < NumModules)%nat -> ~M_defines (Modules n) f);
    PP_find_Some: forall f n, PP_find f = Some n <->  ((n < NumModules)%nat /\ M_defines (Modules n) f)
}.

Lemma PP_no_duplicates: forall (PP:PreProgram) (f:ident) n1 n2, 
            M_defines (Modules PP n1) f -> (n1 < NumModules PP)%nat ->
            M_defines (Modules PP n2) f -> (n2 < NumModules PP)%nat -> n1=n2.
Proof.
   intros.
   assert (N1: PP_find PP f = Some n1). apply (PP_find_Some PP). split; assumption.
   assert (N2: PP_find PP f = Some n2). apply (PP_find_Some PP). split; assumption.
  rewrite N1 in N2. congruence.
Qed.

Definition PP_getFParam (PP:PreProgram) f: Type :=
       match PP_find PP f with
               None => False (*empty type*)
             | Some n =>   match nat_compare n (NumModules PP) with
                                          Lt => FParams PP n 
                                        | _ => False
                                    end
      end.

Definition PP_getVParam (PP:PreProgram) f: Type :=
       match PP_find PP f with
               None => False (*empty type*)
             | Some n =>   match nat_compare n (NumModules PP) with
                                          Lt => VParams PP n 
                                        | _ => False
                                    end
      end.

(*Not sure the above definition help a lot since we'd always have to use type equalities, to get the following def accepted:
Definition PP_lookup (PP:PreProgram) f n: option (globdef  (PP_getFParam PP f) (PP_getVParam PP f)) :=
                   match nat_compare n (NumModules PP) with
                           Lt => M_lookup (Modules PP n) f 
                       | _ =>  None
                  end.*)

(*Here's a definition that works probably a little more smoothly*)
Definition PP_lookup (PP:PreProgram) f n: option (globdef  (FParams PP n) (VParams PP n)) :=
                   match nat_compare n (NumModules PP) with
                           Lt => M_lookup (Modules PP n) f 
                       | _ =>  None
                  end.

Lemma PP_lookup_inv: forall PP f n d, PP_lookup PP f n = Some d -> (n < NumModules PP)%nat /\ M_lookup (Modules PP n) f  = Some d.
  Proof. intros. unfold PP_lookup in H.
             remember (nat_compare n (NumModules PP)) as b.
             destruct b; try inv H.
             split; trivial.
             apply  nat_compare_lt. rewrite Heqb. trivial.
  Qed.

Lemma PP_lookup_intro: forall PP f n,  (n < NumModules PP)%nat -> PP_lookup PP f n = M_lookup (Modules PP n) f.
  Proof. intros. unfold PP_lookup. apply  nat_compare_lt in H. rewrite H. trivial. Qed.

Lemma PP_find_PP_lookup1: forall PP f n, PP_find PP f = Some n -> exists d, PP_lookup PP f n = Some d.
   Proof. intros. apply (PP_find_Some PP f n) in H. destruct H. 
             apply M_defines_iff_M_lookup in H0. destruct H0. exists x.
             apply nat_compare_lt in H. unfold PP_lookup. rewrite H. assumption.
  Qed.

Lemma PP_find_PP_lookup2: forall PP f, PP_find PP f = None-> forall n, (n < NumModules PP)%nat -> PP_lookup PP f n = None.
   Proof. intros. destruct (PP_find_None PP f) as [Z1 _].
              assert (Z2 := Z1 H _ H0).
              unfold PP_lookup. apply nat_compare_lt in H0.  rewrite H0.
              remember (M_lookup (Modules PP n) f) as b.
              destruct b; trivial.
              exfalso. apply Z2. apply M_defines_iff_M_lookup. exists g. rewrite Heqb. trivial.
   Qed.

Record LinkedProgram:= {
    PreProg: PreProgram;
    main : ident;
    main_defined: exists n, PP_find PreProg main = Some n
}.

Section LinkedCoreSemantics.
Variable M:Type. (*type of mem, shared between all running modules*)

Inductive RunningCore:=
  runCore: forall {G C D}, @CoreSemantics G C M D -> G -> C -> RunningCore.

Definition LinkCore:Type :=  list RunningCore.

Parameter  getCore: PreProgram -> (external_function * signature * list val) -> option RunningCore.
(*   runCore MSem Mge Minit ->*)

Parameter PP:PreProgram.
Inductive LinkCoreStep: LinkCore -> M -> LinkCore -> M -> Prop :=
  link_step: forall {G C D} (Sem:@CoreSemantics G C M D)  q m q' m' stack c c' ge, 
          q = runCore Sem ge c ->
          corestep Sem ge c m c' m' ->
          q' = runCore Sem ge c' ->
          LinkCoreStep  (q::stack) m (q'::stack) m'
 | link_call: forall {G C D} (Sem:@CoreSemantics G C M D)  q m q' m' stack c f sig args ge, 
          q = runCore Sem ge c ->
          at_external Sem c = Some(f,sig,args) ->
          getCore PP (f, sig, args) = Some q' ->
          LinkCoreStep  (q::stack) m (q'::q::stack) m'
 | link_ret: forall {G' C' D'} (Sem':@CoreSemantics G' C' M D')  {G C D} (Sem:@CoreSemantics G C M D) 
                                q m q' m' stack c f sig args g g' c' cc qq v,  
          q' = runCore Sem' g' c' ->
          safely_halted Sem' g' c' = Some v ->
          q = runCore Sem g c ->
          at_external Sem c = Some(f,sig,args) -> (*maybe this line can be deleted, since all non-top cores are at_external*)
          after_external Sem (Some v) c = Some cc ->
          qq = runCore Sem g cc ->
          LinkCoreStep  (q'::q::stack) m (qq::stack) m'.

(*An aternative would be to say that linked programs are NEVER at_external, ie to model FULLY linked programs.
  maybe that's more appropriate for Programs (as opposed to PrePrograms? On the other hand, the current choice
  duplicates a little bit what the general extension mechanism does (handling external functions etc.
  But of course, we wanr LinkedSem to be an extension so the coincidence is maybe not too accidental*)
Definition Link_at_external (stack:LinkCore): option (external_function * signature * list val)  :=
   match stack with nil => None
     | (runCore _ _ _ Sem ge c) :: _ => match at_external Sem c with
                                                          None => None
                                                        | Some(f,sig,args) => match getCore PP (f, sig, args) with
                                                                                                     None => Some (f, sig, args)
                                                                                                  | Some q => None (*to ensure no clash with link_call happens*)
                                                                                             end
                                                      end
  end.

  Lemma Link_corestep_not_at_external: forall m q m' q', 
        LinkCoreStep q m q' m' -> Link_at_external q = None.
  Proof. intros.
      inversion H; subst; simpl in *.
      (*step*)
           apply corestep_not_at_external in H1. rewrite H1. trivial.
      (*link_call*)
           rewrite H1. rewrite H2. trivial.
      (*link_ret*)
           assert (Z1:= at_external_halted_excl Sem' g' c').
           destruct Z1. 
               rewrite H0. trivial.
           rewrite H1 in H0. inv H0.
  Qed.

Definition Link_safely_halted (stack:LinkCore): option val :=
   match stack with nil => None
     | (runCore _ _ _ Sem ge c) :: nil => safely_halted Sem ge c
     | _ => None
  end.

  Lemma Link_corestep_not_halted: forall m q m' q', 
      LinkCoreStep q m q' m' -> Link_safely_halted q = None.
  Proof. intros.
      inversion H; subst; simpl in *.
      (*step*)
           apply corestep_not_halted in H1. rewrite H1. destruct stack; trivial.
      (*link_call*)
           assert (Z1:= at_external_halted_excl Sem ge c).
           destruct Z1. rewrite H1 in H0. inv H0.
           rewrite H0. destruct stack; trivial.
      (*link_ret*)
           trivial.
  Qed.

  Lemma Link_at_external_halted_excl: forall q, 
      Link_at_external q = None \/ Link_safely_halted q = None.
  Proof. intros.
       destruct q; simpl.
           left; trivial.
       destruct r; simpl. rename c into Sem. rename c0 into c.
        destruct (at_external_halted_excl Sem g c); rewrite H.
             left; trivial.
             right. destruct q; trivial.
  Qed.
End LinkedCoreSemantics.

