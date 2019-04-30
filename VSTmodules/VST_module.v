Require Import VST.floyd.proofauto.
Require Import linking.

Definition importedFunIds (p:Clight.program): list ident :=
  map fst (filter (fun x => match x with
                              (i, Gfun(External ef inTps outTp cc)) => true
                            | (_,_) => false
                            end)
                  (prog_defs p)).

Definition declaredFunIds (p:Clight.program): list ident :=
  map fst (filter (fun x => match x with
                              (i, Gfun(Internal f)) => true
                            | (_,_) => false
                            end)
                  (prog_defs p)).

Definition globalVarIds (p:Clight.program): list ident :=
  map fst (filter (fun x => match x with
                              (i, Gvar v) => true
                            | (_,_) => false
                            end)
                  (prog_defs p)).

Record ModuleDeclaration := ModuleDecl {
   code:> Clight.program;

   exported: list ident;
   exported_declared: forall i, In i exported -> In i (declaredFunIds code);
   (*ensured by Clight/CompcCert?
   well_formed: NoDup (imported ++ declared); (*also ensured that the 2 lists are distinct*)*)
  
   exported_public: forall i, In i exported -> In i (prog_public code)
}.

Record ClientFacingSpecification := ClientFacingSpec {
   ModDecl :> ModuleDeclaration;
   cmpspecs: compspecs; (*Empty compspecs if no structs/unions are exported, and no static globals exists*)
   ExportSpecs: list funspec;
   ExportSpecs_length: length ExportSpecs = length (exported ModDecl);

   gvar_function: ident -> option (sigT (fun A => A -> val -> mpred));
   gvarAX:
     forall i rep,
       gvar_function i = Some rep ->
       exists v,
         In (i, Gvar v) (prog_defs (code ModDecl)) /\
         exists R: reptype (gvar_info v) -> projT1 rep -> Prop,
         forall x rx,  R x rx <->                
            forall p, (data_at Ews (gvar_info v) x p |--
                    (projT2 rep) rx p) 
}.

Definition especs (CFS: ClientFacingSpecification) : list (ident * funspec) :=
  combine (exported (ModDecl CFS)) (ExportSpecs CFS).
  
Record ModuleImplementationSpecification' := ModuleImplementationSpec' {
   ModCFSpec :> ClientFacingSpecification;
                                                 
   ImportSpecs: list funspec;
   ImportSpecs_length: length ImportSpecs = length (importedFunIds ModCFSpec);
   
   DeclSpecs: list funspec;
   DeclSpecs_length: length DeclSpecs = length (declaredFunIds ModCFSpec)
}. 

Definition ispecs (MS: ModuleImplementationSpecification') : list (ident * funspec) :=
  combine (importedFunIds (ModCFSpec MS)) (ImportSpecs MS).

Definition dspecs (MS: ModuleImplementationSpecification') : list (ident * funspec) :=
  combine (declaredFunIds (ModCFSpec MS)) (DeclSpecs MS).
           
Record ModuleImplementationSpecification := ModuleImplementationSpec {
   ModImplemSpec :> ModuleImplementationSpecification';
   Module_funspecs_sub:
     forall f phi, In (f,phi) (especs ModImplemSpec) ->
                   exists psi, In (f,psi) (dspecs ModImplemSpec) /\
                               TT |-- funspec_sub_si psi phi
}.

(*is computational, so can't define here -- add a characterization?
Definition Gprog_ofImplem (M:ModuleImplementationSpecification) : funspecs :=   
   ltac:(with_library prog (
      (ispecs M) ++ (dspecs M))).*)

Fixpoint entry_of_id {A} (l:list (ident * A)) (i:ident) :=
  match l with
    nil => None
  | (h::t) => if ident_eq i (fst h) then Some (snd h) else entry_of_id t i
  end.

Record ModuleProof := ModulePrf {
  ModSpec:> ModuleImplementationSpecification;
  myGprog : funspecs;
  myVprog : varspecs; 
  bodyproofs: list semax_body_proof ;
  bodyproofs_ok: forall i, In i (declaredFunIds ModSpec) ->
      exists f phi prf, entry_of_id (dspecs ModSpec) i = Some phi /\
                        entry_of_id (prog_defs (code ModSpec)) i = Some (Gfun (Internal f)) /\
                        In (@mk_body myVprog myGprog (cmpspecs ModSpec) f i phi prf) bodyproofs
}.
