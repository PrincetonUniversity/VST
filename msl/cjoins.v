(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.sepalg.

Definition constructive_join_sub {A} {JOIN: Join A} (w1 w3: A) := {w2 | join w1 w2 w3}.

Lemma cjoin_sub_join_sub{A} {JOIN: Join A}: 
    forall {w1 w3}, constructive_join_sub w1 w3 -> join_sub w1 w3.
Proof.
intros.
destruct X as [w2 ?]; exists w2; auto.
Qed.

Lemma cjoin_sub_irr {A} `{Perm_alg A}{CA: Canc_alg A}: 
    forall {w1 w3: A} (j1 j2: constructive_join_sub w1 w3), proj1_sig j1 = proj1_sig j2.
Proof.
intros.
destruct j1 as [w2 ?].
destruct j2 as [w2' ?].
simpl.
apply (join_canc (join_comm j) (join_comm j0)).
Qed.

Lemma cjoin_sub_trans {A} `{Perm_alg A}: forall a b c,
          constructive_join_sub a b -> constructive_join_sub b c -> constructive_join_sub a c.
Proof.
intros.
destruct X as [u ?H].
destruct X0 as [v ?H].
destruct (join_assoc H0 H1) as [f [? ?]].
exists f; auto.
Qed.


Lemma constructive_join_sub_refl {A} `{Perm_alg A}{SA: Sep_alg A}: forall x, constructive_join_sub x x.
Proof.
intros.
destruct (join_ex_units x).
exists x0. apply join_comm; apply u.
Qed.

Hint Resolve @constructive_join_sub_refl.
Definition constructive_joins {A}  {JOIN: Join A} (w1 w2 : A) := {w3 | join w1 w2 w3}.

Lemma cjoins_joins {A}  {JOIN: Join A}: forall {w1 w2}, constructive_joins w1 w2 -> joins w1 w2.
Proof.
intros.
destruct X as [w3 ?]; exists w3; auto.
Qed.

Lemma cjoins_irr {A} `{Perm_alg A}: forall {w1 w2: A} 
    (j1 j2: constructive_joins w1 w2), proj1_sig j1 = proj1_sig j2.
Proof.
intros.
destruct j1 as [w3 ?].
destruct j2 as [w3' ?].
simpl.
apply  (join_eq j j0).
Qed.

Lemma constructive_joins_sym {A} `{Perm_alg A}: forall a b,  
      constructive_joins a b = constructive_joins b a.
Proof.
intros.
unfold constructive_joins.
f_equal.
extensionality w3.
apply prop_ext; split; auto.
Qed.

Definition same_constructive_silhouette {A} {JOIN: Join A} (a b: A) :=
    forall c, (constructive_joins c a -> constructive_joins c b) *
                 (constructive_joins c b -> constructive_joins c a).


  Definition sub_constructive_silhouette {A} {JOIN: Join A}  (a b: A) :=                                                                                       
    forall c, constructive_joins c b -> constructive_joins c a.

  Lemma sub_constructive_silhouette_refl {A} {JOIN: Join A} : forall a, sub_constructive_silhouette a a.                                                                           
  Proof. unfold sub_constructive_silhouette; intuition. Qed.                                                                                      
    
  Lemma sub_constructive_silhouette_trans {A} {JOIN: Join A} : forall a b c,                                                                                          
    sub_constructive_silhouette a b -> sub_constructive_silhouette b c -> sub_constructive_silhouette a c.                                                              
  Proof. unfold sub_constructive_silhouette; intuition. Qed.                                                                                      
      
  Lemma same_constructive_silhouette_refl {A} {JOIN: Join A} : forall a, same_constructive_silhouette a a.                                                                         
  Proof. unfold same_constructive_silhouette; intuition. Qed.                                                                                     
        
  Lemma same_constructive_silhouette_sym {A} {JOIN: Join A}: forall a b,                                                                                             
    same_constructive_silhouette a b -> same_constructive_silhouette b a.                                                                                  
  Proof. unfold same_constructive_silhouette; intuition; destruct (X c); auto. Qed.                                                               
          
  Lemma same_constructive_silhouette_trans {A} {JOIN: Join A}: forall a b c,                                                                                         
    same_constructive_silhouette a b -> same_constructive_silhouette b c -> same_constructive_silhouette a c.
 Proof. unfold same_constructive_silhouette; intuition;
             destruct (X c0); destruct (X0 c0);   auto. Qed.                                                                                   
            
  Lemma same_constructive_silhouette_sub1{A} {JOIN: Join A}: forall a b, 
    same_constructive_silhouette a b -> sub_constructive_silhouette a b.                                                 
  Proof. unfold same_constructive_silhouette, sub_constructive_silhouette; intuition; destruct (X c); auto. Qed.                                               
              
  Lemma same_constructive_silhouette_sub2 {A} {JOIN: Join A}: forall a b,
     same_constructive_silhouette a b -> sub_constructive_silhouette b a.                                                 
  Proof. unfold same_constructive_silhouette, sub_constructive_silhouette; intuition; destruct (X c); auto. Qed. 

                
  Lemma sub_same_constructive_silhouette {A} {JOIN: Join A}: 
    forall a b, sub_constructive_silhouette a b -> sub_constructive_silhouette b a -> same_constructive_silhouette a b.                                                    
  Proof. unfold same_constructive_silhouette, sub_constructive_silhouette; intuition; destruct (H0 c); auto. Qed.
                  
  Lemma same_constructive_silhouette_join {A} `{HA: Perm_alg A}:   
    forall phi phi' phiy phiz phiz',   
      same_constructive_silhouette phi phi' ->                                                                                                
      join phi phiy phiz ->                                                                                                    
      join phi' phiy phiz' ->                                                                                                  
      same_constructive_silhouette phiz phiz'.                                                                                                
  Proof.
    intros * H ? ?.
    intro phiu.                                                                                                                        
    split; intros [phix ?H].                                                                                                            
    destruct (join_assoc H0 (join_comm H2)) as [phif [? ?]].                                                      
    spec H phif.                                                                                                                       
    destruct H as [?H ?H].
    assert (H6: constructive_joins phi phif) by (econstructor; eauto).       
    spec H. rewrite constructive_joins_sym.  auto.                                                                                                  
    clear H5 H6.                                                                                                                       
    destruct H as [phix' ?H].                                                                                                           
    destruct (join_assoc (join_comm H3) H) as [phig [? ?]].                                                         
    generalize (join_eq H1 (join_comm H5)); intro. rewrite <- H7 in *; clear H7 phig.                                                        
    clear H5.                                                                                                                          
    exists phix'.                                                                                                                      
    auto.                                                                                                                              
    destruct (join_assoc H1 (join_comm H2)) as [phif [? ?]].                                                        
    spec H phif.                                                                                                                       
    destruct H as [?H ?H].
    assert (H6: constructive_joins phi' phif) by (econstructor; eauto).                                                                                                         
    spec H5. rewrite constructive_joins_sym.  auto.                                                                                                 
    clear H H6.
    destruct H5 as [phix' ?H].
    destruct (join_assoc (join_comm H3) H) as [phig [? ?]].
    generalize (join_eq H0 (join_comm H5)); intro. rewrite <- H7 in *; clear H7  phig.
    clear H5.
    exists phix'.
    auto.
  Qed.

Lemma constructive_join_sub_joins_trans {A} {JA: Join A}{PA: Perm_alg A}: forall {a b c},
  constructive_join_sub a c -> constructive_joins c b -> constructive_joins a b.
Proof.
intros.
destruct X as [wx X].
destruct X0 as [wy X0].
destruct (join_assoc (join_comm X) X0) as [wf [? ?]].
econstructor; eauto.
Qed.

Lemma join_constructive_join_sub1 {A} {JA: Join A}{PA: Perm_alg A}: forall {a b c},
  join a b c -> constructive_join_sub a c.
Proof. intros; exists b; auto. Qed.

Lemma join_constructive_join_sub2 {A} {JA: Join A}{PA: Perm_alg A}: forall {a b c},
  join a b c -> constructive_join_sub b c.
Proof. intros; exists a; auto. Qed.

Lemma join_constructive_joins {A} {JA: Join A}{PA: Perm_alg A}: forall {a b c},
  join a b c -> constructive_joins a b.
Proof. intros; exists c; auto. Qed.
