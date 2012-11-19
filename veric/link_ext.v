Load loadpath.
Require Import compcert.AST.
Require Import veric.base.
Require Import veric.sim. 
Require Import List.


Section MODULAR_PROGRAMS.
Inductive globdef (F V: Type) : Type :=
      | Gfun (f: F)
      | Gvar (v: globvar V).

Record Module (F V:Type) := mkmodule {
      id_defs: list (ident * globdef F V);
      id_def_unique: forall f gdef1 gdef2,
            In (f,gdef1) id_defs -> In (f,gdef2) id_defs -> gdef1=gdef2
    }.

(*We probably should have a list of "external" globals, and only these have to be
 preserved when envs are compiled (up to reordering perhaps?). 
A nonexternal global may be dropped or added in a compiler pass as needed. 
Only external globals may appear in external events.
Maybe this distinction should be made here, in the def of module, for example as in this definition:*) 
Record Module'(F V:Type) := mkmodule' {
      extern_defs: list (ident * globdef F V); (*inludes exported as well as imported identifiers*)
      exported_ids: list ident; (*the sublist of the externs that are provided by this module, ie the 
             initial memory for this block is allocated during the construction of the genv/initmem for THIS module.*)
      intern_defs: list (ident * globdef F V);
      mod_defs_unique: forall f gdef1 gdef2,
            In (f,gdef1) (extern_defs ++ intern_defs) ->
            In (f,gdef2)  (extern_defs ++ intern_defs) -> gdef1=gdef2;
      exporteds_are_extern: forall f, In f  exported_ids -> exists d, In (f,d) extern_defs;
      interns_not_extern: forall f d, In (f,d)  intern_defs -> ~ In (f,d) extern_defs
    }.

Fixpoint walkFuns {F V}  (l: list (ident * globdef F V)) :  list (ident * F) :=
  match l with nil => nil
     | (id,d)::t => match d with Gfun f => (id,f) :: (walkFuns t) | Gvar _ => walkFuns t end
  end.
Fixpoint walkVars {F V}  (l: list (ident * globdef F V)) :  list (ident * globvar V) :=
  match l with nil => nil
     | (id,d)::t => match d with Gfun _ => (walkVars t) | Gvar v =>  (id,v) :: (walkVars t) end
  end.

Definition mod_funs {F V} (M : Module F V):  list (ident * F) := walkFuns (id_defs _ _ M).
Definition mod_vars {F V} (M : Module F V):  list (ident * globvar V) := walkVars (id_defs _ _ M).
 
Definition mod_funct_names {F V} (M : Module F V):  list ident:= List.map fst (mod_funs M).
Definition mod_var_names {F V} (M : Module F V):  list ident:= List.map fst (mod_vars M).

Fixpoint lookup_ {F V} (l:list (ident * globdef F V)) f :=
   match l with nil => None
     | cons HD TL => match HD with (ff,dd) => if peq ff f then Some dd else lookup_ TL f end
   end.
Lemma lookup_In_funs: forall {F V} (MOD : Module F V) id f,
      lookup_ (id_defs F V MOD) id = Some (Gfun F V f)->
      In (id,f) (mod_funs MOD).
Proof. intros. 
      unfold mod_funs. remember (id_defs F V MOD)  as vl. clear Heqvl MOD.
      induction vl; simpl in *. inv H.
      destruct a. destruct (peq i id); subst. inv H. left; trivial.
      apply IHvl in H. destruct g.  right.  apply H. apply H.
Qed.

Lemma lookup_In_vars: forall {F V} (MOD : Module F V) id v,
      lookup_ (id_defs F V MOD) id = Some (Gvar F V v)->
      In (id,v) (mod_vars MOD).
Proof. intros. 
      unfold mod_vars. remember (id_defs F V MOD)  as vl. clear Heqvl MOD.
      induction vl; simpl in *. inv H.
      destruct a. destruct (peq i id); subst. inv H. left; trivial.
      apply IHvl in H. destruct g. apply H. right.  apply H.
Qed.

(*Here are versions maybe suitable for Module'. defines looks at exported, lookup at all externs ++ interns.
 While we should never need to lookup interns in the linker, we still should ensure that
  no intern is overlaps with interners or externs from other modules, I think*) 
Definition M_defines' {F V} (M:Module' F V) (f:ident): Prop := In f M.(exported_ids _ _ ).
Definition M_lookup' {F V} (M:Module' F V) (f:ident) : option (globdef F V) :=
  lookup_ ((extern_defs _ _ M) ++  (intern_defs _ _ M)) f.

Definition M_defines {F V} (M:Module F V) (f:ident): Prop :=
   exists gdef,  In (f,gdef) M.(id_defs _ _ ).

Definition M_lookup {F V} (M:Module F V) (f:ident) : option (globdef F V) :=
  lookup_ (id_defs _ _ M) f.  

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
(*If we use Module', we should probably add this axiom here, and maybe also add an axiom on type coherence wrt F and V
    between eterns shared by different modules:
    PP_exports_dont_overlap: forall f i j, In f (exported_defs _ _ (Modules i)) ->   In f (exported_defs _ _ (Modules j)) -> i=j*)
}.

Lemma PP_find_LT: forall (PP:PreProgram) f n, PP_find PP f = Some n ->
                                nat_compare n (NumModules PP) = Lt.
  Proof. intros. apply  nat_compare_lt. apply PP_find_Some in H. apply H. Qed.

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
End MODULAR_PROGRAMS.



Section LINKED_SEMANTICS.
(*Do we want to hardcode implementations of builins, virtual loads etc here, or leave that to some other extension?
  For now, I just handle "proper" external functions in the linker*)
Definition get_ident (ef:external_function * signature * list val): option ident :=
match ef with ((f,_),_) =>
  match f with
     EF_external id _ => Some id
  | _ => None
  end
end.

Variable M:Type. (*type of mem, shared between all running modules*)
Record RecSem (F V:Type) := mkRecSem {
      coreTP :Type;
      dataTP: Type;
      ssem: @CoreSemantics (Genv.t F V) coreTP M dataTP
}.

Variable mkSem: forall {F V} (Mod: Module F V), RecSem F V.

Definition SemTable (PP:PreProgram) (n:nat) : option (RecSem (FParams PP n) (VParams PP n)) := 
   match nat_compare n (NumModules PP) with
                    Lt => Some (mkSem _ _ (Modules PP n))
                 | _ => None
   end.

Variable  Genvs: forall {F V} (Mod: Module F V), Genv.t F V. 
Definition GenvsDom (PP:PreProgram): Prop := forall n f d, 
   (n < NumModules PP)%nat -> (M_lookup (Modules PP n) f = Some d-> exists b, Genv.find_symbol (Genvs _ _ (Modules PP n)) f = Some b).
     (*later, we should maybe refine this to distinguish between functions and variables*)

Definition Genvs_wellshared  (PP:PreProgram): Prop := forall n1 f1 d1 n2 f2 d2, 
   (n1 < NumModules PP)%nat -> (M_lookup (Modules PP n1) f1 = Some d1) ->
   (n2 < NumModules PP)%nat -> (M_lookup (Modules PP n2) f2 = Some d2) ->
     ((Genv.find_symbol (Genvs _ _ (Modules PP n1)) f1 = Genv.find_symbol (Genvs _ _ (Modules PP n2)) f2) <-> (f1=f2)).

Inductive RunningCore:=
  runCore: forall {G C D}, @CoreSemantics G C M D -> G -> C -> RunningCore.

Definition  getCore (PP:PreProgram) (ef: external_function * signature * list val): option RunningCore :=
match ef with (_,args) =>
  match (get_ident ef)  with None => None 
  | Some f =>
      match PP_find PP f with None => None
      | Some n => match SemTable PP n with
                              None => None (*shouldn't happen...*)
                           | Some CR => let g := Genvs _ _ (Modules PP n) 
                                                     in match Genv.find_symbol g f with None => None
                                                           | Some b => match make_initial_core  (ssem _ _ CR) g (Vptr b Int.zero)  args with
                                                                                            None => None
                                                                                   | Some c => Some (runCore (ssem _ _ CR) g c)
                                                                                 end
                                                          end
                          end
     end
  end
end. 

(*This should boil down to some basic condition of typing, ie args of right length, etc*)
Definition args_ok (PP:PreProgram) f args := 
forall n b, Genv.find_symbol (Genvs _ _ (Modules PP n)) f = Some b ->
exists c,
    make_initial_core
      (ssem (FParams PP n) (VParams PP n) (mkSem _ _ (Modules PP n)))
      (Genvs _ _ (Modules PP n)) (Vptr b Int.zero) args = Some c.

Lemma getCore_succeeds: forall PP (PP_H1: GenvsDom PP) (PP_H2: Genvs_wellshared PP) 
               f sig args n, PP_find PP f = Some n -> args_ok PP f args ->
               exists RC, getCore PP (EF_external f sig, sig, args) = Some RC.
  Proof. intros.
    unfold getCore. simpl. rewrite H. unfold SemTable. 
      assert (X:= PP_find_LT _ _ _ H).
      rewrite X. 
      apply PP_find_PP_lookup1 in H. destruct H as [d XX].
      destruct (PP_lookup_inv _ _ _ _ XX) as [XX1 XX2].
      destruct (PP_H1 _ _ _ XX1 XX2) as [b Hb]. rewrite Hb.
      apply H0 in Hb. destruct Hb as [c Hc]. rewrite Hc. eexists. reflexivity.
Qed.

Definition LinkCore:Type :=  list RunningCore.

Variable PP:PreProgram.
Inductive LinkCoreStep: unit -> LinkCore -> M -> LinkCore -> M -> Prop :=
  link_step: forall {G C D} (Sem:@CoreSemantics G C M D)  q m q' m' stack c c' ge, 
          q = runCore Sem ge c ->
          corestep Sem ge c m c' m' ->
          q' = runCore Sem ge c' ->
          LinkCoreStep  tt (q::stack) m (q'::stack) m'
 | link_call: forall {G C D} (Sem:@CoreSemantics G C M D)  q m q' m' stack c f sig args ge, 
          q = runCore Sem ge c ->
          at_external Sem c = Some(f,sig,args) ->
          getCore PP (f, sig, args) = Some q' ->
          LinkCoreStep  tt (q::stack) m (q'::q::stack) m'
 | link_ret: forall {G' C' D'} (Sem':@CoreSemantics G' C' M D')  {G C D} (Sem:@CoreSemantics G C M D) 
                                q m q' m' stack c f sig args g g' c' cc qq v,  
          q' = runCore Sem' g' c' ->
          safely_halted Sem' g' c' = Some v ->
          q = runCore Sem g c ->
          at_external Sem c = Some(f,sig,args) -> (*maybe this line can be deleted, since all non-top cores are at_external*)
          after_external Sem (Some v) c = Some cc ->
          qq = runCore Sem g cc ->
          LinkCoreStep tt (q'::q::stack) m (qq::stack) m'.

(*An aternative would be to say that linked programs are NEVER at_external, ie to model FULLY linked programs.
  maybe that's more appropriate for Programs (as opposed to PrePrograms? On the other hand, the current choice
  duplicates a little bit what the general extension mechanism does (handling external functions etc.
  But of course, we wanr LinkedSem to be an extension so the coincidence is maybe not too accidental*)
Definition Link_at_external (stack:LinkCore): option (external_function * signature * list val)  :=
   match stack with nil => None
     | (runCore G C D Sem ge c) :: _ => match at_external Sem c with
                                                          None => None
                                                        | Some(f,sig,args) => match getCore PP (f, sig, args) with
                                                                                                     None => Some (f, sig, args)
                                                                                                  | Some q => None (*to ensure no clash with link_call happens*)
                                                                                             end
                                                      end
  end.

  Lemma Link_corestep_not_at_external: forall g m q m' q', 
        LinkCoreStep g q m q' m' -> Link_at_external q = None.
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

Definition Link_safely_halted (_:unit) (stack:LinkCore): option val :=
   match stack with nil => None
     | (runCore _ _ _ Sem ge c) :: nil => safely_halted Sem ge c
     | _ => None
  end.

  Lemma Link_corestep_not_halted: forall g m q m' q', 
      LinkCoreStep g q m q' m' -> Link_safely_halted g q = None.
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

  Lemma Link_at_external_halted_excl: forall g q, 
      Link_at_external q = None \/ Link_safely_halted g q = None.
  Proof. intros.
       destruct q; simpl.
           left; trivial.
       destruct r; simpl. rename c into Sem. rename c0 into c.
        destruct (at_external_halted_excl Sem g0 c); rewrite H.
             left; trivial.
             right. destruct q; trivial.
  Qed.

Definition Link_after_external (rv:option val) (stack: LinkCore) : option LinkCore :=
   match stack with nil => None
     | (runCore _ _ _ Sem ge c) :: stk  => match after_external Sem rv c with
                                                                             None => None
                                                                           | Some cc => Some ((runCore Sem ge cc) :: stk)
                                                                   end
  end.

Variable D_values: forall i, dataTP _ _ (mkSem _ _ (Modules PP i)).

(*For Programs, take/require D to be the D of the module Nmain defining main, so that d is of the right type, and the require d = D_values Nmain*)
Definition Link_initial_mem (D:Type) (_:unit) (m: M) (d: D) : Prop :=
    forall i, (i < NumModules PP)%nat -> initial_mem (ssem _ _ (mkSem _ _ (Modules PP i))) (Genvs _ _ (Modules PP i)) m (D_values i).

Variable Link_make_initial_core: unit -> val -> list val -> option LinkCore.
   (*for now unimplemented. Once we have a Program, take the initcore of Main*)

Definition LinkSem (D:Type) : CoreSemantics unit LinkCore M D.
  eapply Build_CoreSemantics with (at_external := Link_at_external)(safely_halted := Link_safely_halted)(corestep:=LinkCoreStep).
      apply  Link_initial_mem.
      apply Link_make_initial_core.
      apply Link_after_external.
      apply Link_corestep_not_at_external.
      apply Link_corestep_not_halted.
      apply Link_at_external_halted_excl.
Defined.

(*Meaningful theorems will probably use the following 2 properties:*)
Parameter PP_H1: GenvsDom PP.
Parameter PP_H2: Genvs_wellshared PP.
End LINKED_SEMANTICS.
Check LinkSem.

(* Old stuff on merged genvs.
Variable Fparams: nat -> Type.
Variable Vparams: nat -> Type.
Variable GenvType : Type -> Type -> Type. (*will be Genv.t*)
Section MKGENV.
Parameter PP:PreProgram.
Parameter Genvs : forall (n:nat), GenvType (FParams PP n) (VParams PP n).

Parameter lookup (G:Genvs) (f:ident), 
Check Genv.genv_symb.
  genv_symb: PTree.t block;        
Definition lookup1 (n:nat): block -> option (globvar (VParams PP n)) := (Genv.find_var_info (Genvs n)).
Definition lookup (b:block) : option (globvar {t | exists n, t=VParams PP n}).
  remember (find_if

Inductive plusTp (X Y:Type):Type :=
  isX: X ->  plusTp X Y
| isY: Y -> plusTp X Y.

Inductive listTp: list Type -> Type :=
   nilTP: listTp nil
| consTP: forall tp tps, tp -> listTp (tp::tps).
Check consTP.
Fixpoint natTp (TPs : nat -> Type) M: Type :=
  match M with
      O => forall (x:TPs O), consTP (TPs O) nil
    | S n => consTP (TPs O) nilTP
  end.
Section MergeGenv.
Variable Fparams: nat -> Type.
Variable Vparams: nat -> Type.
Variable Genvs : forall (n:nat), Genv.t (Fparams n) (Vparams n).

Definition lookup1 (n:nat): block -> option (globvar (Vparams n)) := (Genv.find_var_info (Genvs n)).

Program Definition add_function (ge: Genv.t) (n:nat) (idf: ident * (Fparams n)) : Genv.t :=
   Genv.add_function ge idf.

Program Definition add_function (ge: t) (idf: ident * F) : t :=

*)

(*Module Lenv.
(*Maybe something like this:*)
Record t (F V:Type) : Type := mklenv {
  low : block; (*is the first block used*)
  high : block; (* last used block*)
  mid : block; (*boundary between functions and vars*)
  lenv_symb: PTree.t block;             (**r mapping symbol -> block *)
  lenv_funs: ZMap.t (option F);         (**r mapping function pointer -> definition *)
  lenv_vars: ZMap.t (option (globvar V)); (**r mapping variable pointer -> info *)
  lenv_nextfun: block;                  (**r next function pointer *)
  lenv_nextvar: block;                  (**r next variable pointer *)
(* genv has this: 
   genv_nextfun_neg: genv_nextfun < 0;
  genv_nextvar_pos: genv_nextvar > 0;
*)
  low_pos: 0 < low;
  lenv_nextfun_neg: low <= lenv_nextfun < mid;
  lenv_nextvar_pos: mid <= lenv_nextvar <= high;
(*  lenv_symb_range: forall id b, PTree.get id lenv_symb = Some b -> b <> 0 /\ lenv_nextfun < b /\ b < lenv_nextvar;
  lenv_funs_range: forall b f, ZMap.get b lenv_funs = Some f -> lenv_nextfun < b < 0;
  lenv_vars_range: forall b v, ZMap.get b lenv_vars = Some v -> 0 < b < lenv_nextvar;*)
  lenv_symb_range: forall id b, PTree.get id lenv_symb = Some b -> low <= b <= lenv_nextfun \/  mid <= b <= lenv_nextvar;
  lenv_funs_range: forall b f, ZMap.get b lenv_funs = Some f -> low <= b <= lenv_nextfun;
  lenv_vars_range: forall b v, ZMap.get b lenv_vars = Some v -> mid <= b <= lenv_nextvar;
  lenv_vars_inj: forall id1 id2 b, 
    PTree.get id1 lenv_symb = Some b -> PTree.get id2 lenv_symb = Some b -> id1 = id2
}.

(*And now, restate and reprove the lemmas from Globalenv*)

(*Then, define construction of a single local env*)
Parameter localenv: forall {F V} (MOD: Module F V), t F V.

(*allocate (dintinctly) localenvs  for all modules in preprogram*)
Parameter mk_lenvs: forall (PP:PreProgram)  (n:nat), t (FParams PP n) (VParams PP n).
Axiom localenvs_distinct: forall (PP:PreProgram)  n (H: (S n < NumModules PP)%nat),
                high _ _ (mk_lenvs PP n) < low _ _ (mk_lenvs PP (S n)).
End Lenv.

Section LOCAL_ENV.
  (*Just to test , let's use a simple aadapation of genv constrution - but it doesn't esnure that functions and variables
    of different modules are laid out in nonoverlapping style!*)
Definition localenv {F V} (MOD: Module F V): Genv.t F V:=
   Genv.add_variables (Genv.add_functions (Genv.empty_genv F V) (mod_funs MOD)) (mod_vars MOD).


(*from Theorem Genv.find_symbol_exists:*)
Theorem local_find_modvars_exists:
  forall {F V} (MOD:Module F V) id gv,
  In (id, gv) (mod_vars MOD) ->
  exists b, Genv.find_symbol (localenv MOD) id = Some b.
Proof.
  intros until gv.
  assert (forall vl ge,
          (exists b, @Genv.find_symbol F V ge id = Some b) ->
          exists b, Genv.find_symbol (Genv.add_variables ge vl) id = Some b).
  unfold Genv.find_symbol; induction vl; simpl; intros. auto. apply IHvl.
  simpl. rewrite PTree.gsspec. fold ident. destruct (peq id (fst a)).
  exists (Genv.genv_nextvar ge); auto. auto.

  assert (forall vl ge, In (id, gv) vl ->
          exists b, Genv.find_symbol (@Genv.add_variables F V ge vl) id = Some b).
  unfold Genv.find_symbol; induction vl; simpl; intros. contradiction.
  destruct H0. apply H. subst; unfold Genv.find_symbol; simpl.
  rewrite PTree.gss. exists (Genv.genv_nextvar ge); auto.
  eauto.

  intros. unfold localenv; eauto. 
Qed.

Lemma local_find_addfun: forall {F V} vl (g:Genv.t F V)  id b, 
   Genv.find_symbol g id = Some b ->
   exists bb, Genv.find_symbol (Genv.add_functions g vl) id = Some bb.
Proof. intros F V vl.
  unfold Genv.find_symbol; induction vl; simpl; intros. exists b. trivial.
  destruct a.
  destruct (ident_eq id i). subst. eapply IHvl. simpl.  rewrite PTree.gss. reflexivity.
  eapply (IHvl _ _ b). simpl. rewrite PTree.gso. trivial. trivial.
Qed.

Lemma local_find_funs_exists: forall F V vl id gv (g:Genv.t F V),
   In (id, gv) vl ->
  exists b : block,
   Genv.find_symbol (Genv.add_functions g vl) id = Some b.
Proof.
  intros until gv.
  unfold Genv.find_symbol; induction vl; simpl; intros. contradiction.
  destruct H. subst. eapply local_find_addfun.
         unfold Genv.find_symbol. simpl.   rewrite PTree.gss. reflexivity.
  eauto.
Qed.

Theorem local_find_modfuns_exists:
  forall {F V} (MOD:Module F V) id gv,
  In (id, gv) (mod_funs MOD) ->
  exists b, Genv.find_symbol (localenv MOD) id = Some b.
Proof.
  intros until gv. unfold localenv. 
  assert (forall vl ge,
          (exists b, @Genv.find_symbol F V ge id = Some b) ->
          exists b, Genv.find_symbol (Genv.add_variables ge vl) id = Some b).
      unfold Genv.find_symbol; induction vl; simpl; intros. auto.
      apply IHvl.
      simpl. rewrite PTree.gsspec. fold ident. destruct (peq id (fst a)).
      exists (Genv.genv_nextvar ge); auto. auto.
  intros.
  eapply (H (mod_vars MOD)). eapply (local_find_funs_exists _ _ _ _  _ _ H0).
Qed.

(*Maybe laterwe'll need somehting like this, cf Theorem Genv.find_var_exists:
Theorem local_find_functs_exists:
  forall {F V} (MOD:Module F V)  id gv,
  list_norepet (mod_var_names MOD) ->
  In (id, gv) (mod_vars MOD) ->
  exists b,
     Genv.find_symbol (localenv MOD) id = Some b
  /\ Genv.find_var_info (localenv MOD) b = Some gv.*)

Lemma localenv_sound : forall{F V} (MOD:Module F V) f d, 
            M_lookup MOD f = Some d -> exists b, Genv.find_symbol (localenv MOD) f  = Some b.
  Proof. intros.
     unfold  M_lookup in H.
     destruct d.
       eapply local_find_modfuns_exists. apply lookup_In_funs. apply H.
       eapply local_find_modvars_exists. apply lookup_In_vars. apply H.
Qed.
End LOCAL_ENV.*)