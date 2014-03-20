Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import linking.sepcomp. Import SepComp.

Lemma reestablish_locBlocksSrc mu0 mu : 
  locBlocksSrc (reestablish mu0 mu) = locBlocksSrc mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_locBlocksTgt mu0 mu : 
  locBlocksTgt (reestablish mu0 mu) = locBlocksTgt mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_pubBlocksSrc mu0 mu : 
  pubBlocksSrc (reestablish mu0 mu) = pubBlocksSrc mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_pubBlocksTgt mu0 mu : 
  pubBlocksTgt (reestablish mu0 mu) = pubBlocksTgt mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_extBlocksSrc mu0 mu : 
  extBlocksSrc (reestablish mu0 mu) 
  = (fun b => if locBlocksSrc mu0 b then false else DomSrc mu b).
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_extBlocksTgt mu0 mu : 
  extBlocksTgt (reestablish mu0 mu) 
  = (fun b => if locBlocksTgt mu0 b then false else DomTgt mu b).
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_frgnBlocksSrc mu0 mu : 
  frgnBlocksSrc (reestablish mu0 mu) 
  = frgnBlocksSrc mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_frgnBlocksTgt mu0 mu : 
  frgnBlocksTgt (reestablish mu0 mu) 
  = frgnBlocksTgt mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_local_of mu0 mu :
  local_of (reestablish mu0 mu) = local_of mu0.
Proof. by case: mu0; case: mu. Qed.

Lemma reestablish_extern_of mu0 mu :
  extern_of (reestablish mu0 mu) 
  = (fun b => if locBlocksSrc mu0 b then None 
              else as_inj mu b).
Proof. by case: mu0; case: mu. Qed.

