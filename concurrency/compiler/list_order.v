Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Wellfounded.
Import Basics.
Import Relation_Operators.

Require Import compcert.lib.Coqlib.



     (*  The order on the lists is not lexicographic!
         It's Every element is smaller or equal.
         ALSO : surprisingly, we don't need transitivity.       
         
       *)
      Inductive list_ord {A} (ord: A -> A -> Prop): list A -> list A -> Prop:=
      | lt_head: forall x y ls, ord x y -> list_ord ord (x::ls) (y::ls)
      | lt_tail: forall x ls ls', list_ord ord ls ls' ->
                             list_ord ord (x::ls) (x::ls').
      Inductive list_ord_part {A}
                (list_ord: list A -> list A -> Prop)
                (ord: A -> A -> Prop): list A -> list A -> Prop:=
      | lt_head_part: forall x y ls, ord x y ->
                                list_ord_part list_ord ord (x::ls) (y::ls)
      | lt_tail_part: forall x ls ls', list_ord ls ls' ->
                                  list_ord_part list_ord ord (x::ls) (x::ls').
      
      Inductive list_ord_trans {A} (ord: A -> A -> Prop): list A -> list A -> Prop:=
      | lt_head_trans: forall x y ls, ord x y -> list_ord_trans ord (x::ls) (y::ls)
      | lt_tail_trans: forall x ls ls', list_ord_trans ord ls ls' ->
                             list_ord_trans ord (x::ls) (x::ls')
      | lt_all: forall x y ls ls', ord x y ->
                              list_ord_trans ord ls ls' ->
                              list_ord_trans ord (x::ls) (y::ls').
      Instance list_ord_is_trans {A} (ord: relation A):
        Transitive ord -> Transitive (list_ord_trans ord).
      Proof.
        intros Trans ?? z H1; revert z.
        induction H1; intros z Hz; inv Hz;
          first [constructor 1|
                 constructor 2|
                 constructor 3]; eauto.
      Qed. 

      Definition trans_symprod {A B} ltA ltB : relation (A * B):=
        Relation_Operators.clos_trans _ (@Relation_Operators.symprod A B ltA ltB).
      Lemma trans_symprod_wf:
         forall {A B} (leA : relation A) (leB : relation B),
       well_founded leA -> well_founded leB -> 
       well_founded (trans_symprod leA leB).
      Proof. intros; apply wf_clos_trans, wf_symprod; eauto. Qed.
      
      Definition ord_union_intersection {A B} ltA ltB : relation (A * B):=
        Relation_Operators.clos_trans _ (@Relation_Operators.symprod A B ltA ltB).
      
      Lemma list_order_as_pair:
        forall {A} ord (a b:A) lsa lsb,
          list_ord ord (a::lsa) (b::lsb) <->
          symprod _ _ ord (list_ord ord) (a,lsa) (b,lsb).
      Proof.
        split; intros **. 
        - inv H.
          + left; assumption.
          + right; assumption.
        - remember (a,lsa) as alsa.
          remember (b,lsb) as blsb.
          set (listify:= fun a_lsa: (A * list A)=> (fst a_lsa) :: (snd a_lsa)). 
          replace (a::lsa) with (listify alsa) by
           (unfold listify; subst; reflexivity).
          replace (b::lsb) with (listify blsb) by
              (unfold listify; subst; reflexivity).
          clear Heqalsa Heqblsb.
          induction H.
          + apply lt_head; assumption.
          + apply lt_tail; assumption.
      Qed.
      Lemma list_order_part_as_pair:
        forall {A} list_ord ord (a b:A) lsa lsb,
          list_ord_part list_ord ord (a::lsa) (b::lsb) <->
          symprod _ _ ord list_ord (a,lsa) (b,lsb).
      Proof.
        split; intros **. 
        - inv H.
          + left; assumption.
          + right; assumption.
        - remember (a,lsa) as alsa.
          remember (b,lsb) as blsb.
          set (listify:= fun a_lsa: (A * list A)=> (fst a_lsa) :: (snd a_lsa)). 
          replace (a::lsa) with (listify alsa) by
           (unfold listify; subst; reflexivity).
          replace (b::lsb) with (listify blsb) by
              (unfold listify; subst; reflexivity).
          clear Heqalsa Heqblsb.
          induction H.
          + apply lt_head_part; assumption.
          + apply lt_tail_part; assumption.
      Qed.   
      
      Lemma list_order_trans_as_pair:
        forall {A} ord (a b:A) lsa lsb,
          Transitive ord ->
          list_ord_trans ord (a::lsa) (b::lsb) <->
          trans_symprod ord (list_ord_trans ord) (a,lsa) (b,lsb).
      Proof.
        split; intros **. 
        - inv H0.
          + eapply t_step; left; assumption.
          + eapply t_step; right; assumption.
          + eapply Relation_Operators.t_trans.
            * eapply Relation_Operators.t_step.
              left; eassumption.
            * eapply Relation_Operators.t_step.
              right; eassumption.
        - remember (a,lsa) as alsa.
          remember (b,lsb) as blsb.
          set (listify:= fun a_lsa: (A * list A)=> (fst a_lsa) :: (snd a_lsa)). 
          replace (a::lsa) with (listify alsa) by
           (unfold listify; subst; reflexivity).
          replace (b::lsb) with (listify blsb) by
              (unfold listify; subst; reflexivity).
          clear Heqalsa Heqblsb.
          induction H0. inv H0.
          + apply lt_head_trans; assumption.
          + apply lt_tail_trans; assumption.
          + eapply list_ord_is_trans; eauto.
      Qed.

      (* List order annotated with length. *)
      Definition ln_ord {A} (ord: (list A) -> (list A) -> Prop) n:=
        fun ls1 ls2 =>
          length ls1 = n /\ length ls2 = n /\ ord ls1 ls2.
      
      Lemma well_founded_by_length:
        forall {A} (ord: relation A) ,
        (forall n, forall x, length x = n ->
              Acc (list_ord ord) x) ->
        well_founded (list_ord ord).
      Proof. intros ** ?; eapply H; reflexivity. Qed.
        

      Lemma list_ord_length:
        forall {A} (ord: relation A) y x,
          list_ord ord y x ->
          length y = length x.
      Proof.
        intros. revert y H.
        induction x; intros; inv H.
        all: simpl; f_equal; eauto.
      Qed.
      
      Lemma ln_ord_inversion:
        forall {A} (ord: relation A) n y x,
          length x = n ->
          list_ord ord y x ->
          ln_ord (list_ord ord) n y x.
      Proof.
        repeat split; auto.
        - erewrite list_ord_length; eauto.
      Qed.
      
      Lemma wf_list_helper:
        forall {A} (ord: relation A) n,
          (forall x : list A, Acc (ln_ord (list_ord ord) n) x) ->
          forall x : list A,
            Datatypes.length x = n -> Acc (list_ord ord) x.
      Proof.
        intros ? ? ? ? x.
        eapply (@Acc_ind _ (ln_ord (list_ord ord) n)
                         (fun x => length x = n -> Acc (list_ord ord) x) 
                         
               ); eauto.
        clear x; intros.
        econstructor; intros.
        eapply H1.
        - apply ln_ord_inversion; eauto.
        - erewrite list_ord_length; eauto.
      Qed.

        
      Lemma wf_list_ord_n:
        forall {A} (ord:A -> A -> Prop),
        (forall n, well_founded (ln_ord (list_ord ord) n)) ->
        well_founded (list_ord ord).
      Proof.
        intros ** ?.
        eapply wf_list_helper; try reflexivity. eapply H.
      Qed.
          
      Local Instance well_founded_subrelation {A}
        : Proper (flip subrelation ==> impl) (@well_founded A).
      Proof.
        intros R R' HR Rwf a.
        induction (Rwf a) as [a Ra R'a].
        constructor; intros y Hy.
        apply R'a, HR, Hy.
      Qed.

      Definition pair_to_list {A} (als: A *list A ): list A :=
        match als with | (a, ls) => a:: ls end.
      Definition comp_ord {A B} (ord:relation A) (f: B -> A): relation B:=
        fun b1 b2 => ord (f b1) (f b2).
      Lemma trans_symprod_length:
        forall {A} (ord: relation A) x y,
          trans_symprod ord (list_ord ord) x y ->
          length (pair_to_list y) = length (pair_to_list x).
      Proof.
        intros.
        induction H. inv H.
        - reflexivity.
        - simpl. eapply list_ord_length in H0; eauto.
        - etransitivity; eauto.
      Qed.
      Lemma comp_ord_subrelation:
        forall {A} ls_ord (ord: relation A),
          (relation_equivalence)
            (symprod _ _ ord (ls_ord))
            (comp_ord (list_ord_part ls_ord ord) pair_to_list).
      Proof.
        intros ** [] []; split; intros H. 
        - inv H; constructor; auto.
        - inv H; constructor; auto.
      Qed.
      
      Lemma rel_equiv:
        forall {A} (ord: relation A) n,
          (flip subrelation)
            (symprod _ _ ord (ln_ord (list_ord ord) n))
            (comp_ord (ln_ord (list_ord ord) (S n)) pair_to_list).
      Proof.
        intros ** [] []; simpl. 
        - intros (?&?&?).
          eapply list_order_as_pair in H1.
          induction H1. 
          + constructor; auto.
          + constructor.
            repeat (split; eauto).
      Qed.
      Lemma wf_comp_ord_filter:
        forall {A B} (ord:relation A) (f: B -> A) (P: A -> Prop),
          (forall a, P a -> exists b, f b = a) ->
          well_founded (comp_ord ord f) ->
          (forall a b, ord a b -> P a) ->
          (forall a b, ord a b -> P b) ->
          well_founded ord.
      Proof.
        intros ?? ord f P H Hwf ? ? a.
        econstructor; intros.
        pose proof (H0 _ _ H2) as Py.
        destruct (H y Py) as (b & fb); rewrite <- fb.
        clear Py fb a y H2.
        eapply (@Acc_ind _ (comp_ord ord f)
                         (fun b => Acc ord (f b))); eauto.
        - intros.
          econstructor; intros.
          pose proof (H0 _ _ H4) as Py.
          destruct (H y Py) as (b' & fb'); rewrite <- fb' in *.
          eapply H3; eauto.
      Qed.

      
      Lemma pair_to_list_pimg:
          forall A (a : list A), a <> nil ->
                        exists b : A * list A, pair_to_list b = a.
      Proof.
        intros. destruct a; try (contradict H; reflexivity).
        exists (a,a0); reflexivity.
      Qed.
      Lemma list_ord_wf:
        forall {A} (ord:A->A->Prop),
          well_founded ord ->
          well_founded (list_ord ord).
      Proof.
        intros.
        eapply wf_list_ord_n.
        induction n.
        - intros ** a. destruct a.
          + constructor; intros ? (?&?&?). inv H2.
          + constructor; intros ? (?&?&?). inv H1.
        - eapply wf_comp_ord_filter;
            try apply pair_to_list_pimg.
          
          + erewrite <- rel_equiv; eapply wf_symprod; auto.
          + intros ?? (?&?&?) ?; subst; simpl in *;congruence.
          + intros ?? (?&?&?) ?; subst; simpl in *;congruence.
      Qed.

      Lemma list_ord_part_wf:
        forall {A} list_ord (ord:A->A->Prop),
          well_founded ord ->
          well_founded list_ord ->
          well_founded (list_ord_part list_ord ord).
      Proof.
        intros.
        eapply wf_comp_ord_filter;
          try apply pair_to_list_pimg.
        - erewrite <- comp_ord_subrelation; apply wf_symprod; assumption.
        - intros ** Heq; subst; simpl in *. inv H1.
        - intros ** Heq; subst; simpl in *. inv H1.
      Qed.

      
      