Require Import VST.floyd.proofauto.
(*Require Import sha.spec_sha.*)
Require Import sha.spec_hmac.
Require Import hmacdrbg.hmac_drbg.
Require Import sha.vst_lemmas.

Ltac make_cs_preserve' :=
 match goal with |- change_composite_env ?a ?b =>
  make_cs_preserve a b
end.

Global Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Global Instance CompSpecs_Preserve: change_composite_env
      spec_hmac.CompSpecs CompSpecs := ltac:(make_cs_preserve').
Global Instance CompSpecs_Preserve': change_composite_env 
             CompSpecs spec_hmac.CompSpecs := ltac:(make_cs_preserve').

Lemma change_compspecs_data_block: forall sh v p,
  @data_block spec_hmac.CompSpecs sh v p ⊣⊢
  @data_block CompSpecs sh v p.
Proof.
  intros.
  unfold data_block.
  apply data_at_change_composite; auto.
Qed.

Ltac change_compspecs' cs cs' ::=
  match goal with
  | |- context [@data_block cs'] => rewrite change_compspecs_data_block
  | |- context [data_at(cs := cs') ?sh ?t ?v1] => erewrite (data_at_change_composite(cs_from := cs') (cs_to := cs) sh t); [| apply JMeq_refl | reflexivity]
  | |- context [field_at(cs := cs') ?sh ?t ?gfs ?v1] => erewrite (field_at_change_composite(cs_from := cs') (cs_to := cs) sh t gfs); [| apply JMeq_refl | reflexivity]
  | |- context [data_at_(cs := cs') ?sh ?t] => erewrite (data_at__change_composite(cs_from := cs') (cs_to := cs) sh t); [| reflexivity]
  | |- context [field_at_(cs := cs') ?sh ?t ?gfs] => erewrite (field_at__change_composite(cs_from := cs') (cs_to := cs) sh t gfs); [| reflexivity]
  | |- context [?A cs'] => change (A cs') with (A cs)
  | |- context [?A cs' ?B] => change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => change (A cs' B C D E F) with (A cs B C D E F)
 end.
