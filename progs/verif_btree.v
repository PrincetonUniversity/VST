Require Import floyd.proofauto. (* Import the Verifiable C system *)
Require Import verif_bin_search.
Require Import progs.btree. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Inductive bnode :=
| BNode (keys : list Z) (children : list bnode).

Section bnode_rect.

  Variables (P : bnode -> Type) (Q : list bnode -> Type)
(*            (Hleaf : forall v, P (BLeaf v))*)
            (Hint : forall keys children, Q children -> P (BNode keys children))
            (Hnil : Q nil) (Hcons : forall t l, P t -> Q l -> Q (t :: l)).

  Fixpoint btree_rect t :=
    match t as t0 return (P t0) with
(*    | BLeaf v => Hleaf v*)
    | BNode keys children => Hint keys children (list_rect Q Hnil
                            (fun u r => Hcons u r (btree_rect u)) children)
    end.
  
End bnode_rect.

Lemma btree_ind (P : bnode -> Prop) (*(Hleaf : forall v, P (BLeaf v))*)
      (Hint : forall keys children, Forall P children -> P (BNode keys children)) t : P t.
Proof.
  induction t using btree_rect with (Q := Forall P); auto.
Qed.

Section BTree.

  Parameter d : nat.
  Hypothesis d_min : (1 <= d)%nat.

  (* could use bin_search here instead *)

  Inductive find_result := Found (i : nat) | NotFound (i : nat).
  
  Fixpoint find_index tgt keys :=
    match keys with
    | [] => NotFound O
    | k :: rest => if tgt <? k then NotFound O
        else if tgt =? k then Found O
        else match find_index tgt rest with
             | Found i => Found (S i)
             | NotFound i => NotFound (S i)
             end
    end.

  Fixpoint find_path tgt t :=
    let search_nth := fix f children i :=
      match children, i with
      | [], _ => None
      | c :: _, O => find_path tgt c
      | _ :: rest, S i => f rest i
      end in
    match t with BNode keys children =>
      match find_index tgt keys with
      | NotFound i => match search_nth children i with
                      | Some p => Some (i :: p)
                      | None => None
                      end
      | Found i => Some [i]
      end
    end.

  Definition search tgt t := match find_path tgt t with Some _ => true | None => false end.
  
  Definition replace {A} i (x : A) l := firstn i l ++ x :: skipn (S i) l.
  
  Fixpoint find_leaf tgt t :=
    let find_nth := fix f children i :=
      match children, i with
      | [], _ => Some []
      | c :: _, O => find_leaf tgt c
      | _ :: rest, S i => f rest i
      end in
    match t with BNode keys children =>
      match find_index tgt keys with
      | NotFound i => match find_nth children i with
                      | Some p => Some (i :: p)
                      | None => None
                      end
      | Found _ => None
      end
    end.

  Definition split parent i :=
    match parent with BNode keys children =>
      match nth_error children i with
      | Some (BNode keys' children') =>
        let mid := (length keys' / 2)%nat in
        BNode (insert i (nth mid keys' 0) keys)
              (insert i (BNode (firstn mid keys') (firstn (S mid) children'))
              (replace i (BNode (skipn (S mid) keys') (skipn (S mid) children')) children))
      | None => parent
      end
    end.
  
  Fixpoint insert_at tgt t path :=
    match path with
    | [] => None
    | [i] => match t with BNode keys children => Some (BNode (insert i tgt keys) children)
             end
    | [i; j] => match t with BNode keys children =>
        match nth_error children i with
        | Some (BNode keys' []) =>
          let t' := BNode keys (replace i (BNode (insert j tgt keys') []) children) in
          if lt_dec (length keys') (2 * d) then Some t'
          else Some (split t' i)
        | _ => None
        end end
    | i :: rest => match t with BNode keys children =>
        match nth_error children i with
        | Some c => match insert_at tgt c rest with
                    | Some (BNode keys' children') =>
                      let t' := BNode keys (replace i (BNode keys' children') children) in
                      if le_dec (length keys') (2 * d) then Some t'
                      else Some (split t' i)
                    | None => None
                    end
        | _ => None
        end end
    end.

  Definition b_insert tgt t :=
    match find_leaf tgt t with
    | Some p => match insert_at tgt t p with
                | Some t' => match t' with BNode keys children =>
                               if le_dec (length keys) (2 * d) then Some t'
                               else Some (split (BNode [] [t']) 0)
                             end
                | None => None
                end
    | None => None
    end.

  Definition remove_at {A} i (l : list A) := firstn i l ++ skipn (S i) l.

  Fixpoint del_max t :=
    let del_last := fix f children :=
      match children with
      | [] => (BNode [] [], 0, None)
      | [c] => del_max c
      | _ :: rest => f rest
      end in
    match t with
    | BNode keys [] => (BNode (removelast keys) [], last keys 0,
                        if le_dec (length keys) d then Some [] else None)
    | BNode keys children => let '(t', v, p) := del_last children in
        (BNode keys (replace (length children - 1) t' children),
         v, match p with Some p => Some ((length children - 1)%nat :: p)
                    | None => None end)
    end.

  Definition merge t i j := match t with BNode keys children =>
    let sep := nth i keys 0 in
    match nth i children (BNode [] []) with BNode keysl childrenl =>
    match nth j children (BNode [] []) with BNode keysr childrenr =>
    let l' := BNode (keysl ++ sep :: keysr) (childrenl ++ childrenr) in
    if eq_dec (length keys) (S O) then l'
    else BNode (remove_at i keys) (remove_at j (replace i l' children))
    end end end.                                     
  
  Definition tryleft t i :=
    match i with
    | O => merge t O (S O)
    | S i' => match t with BNode keys children =>
        match nth_error children i' with
        | Some (BNode keysl childrenl) =>
          if lt_dec d (length keysl) then
            let sep := nth i' keys 0 in
            match nth_error children i with
            | Some (BNode keys' children') =>
              let c' := BNode (sep :: keys')
                              (match childrenl with [] => children' |
                               _ => last childrenl (BNode [] []) :: children' end) in
              BNode (replace i' (last keysl 0) keys)
                    (replace i' (BNode (removelast keysl) (removelast childrenl))
                             (replace i c' children))
            | None => t
            end
          else merge t i' i
        | None => t
        end end
    end.

  Definition rebalance_local t i := match t with BNode keys children =>
    match nth_error children (S i) with
    | Some (BNode (k :: keysr) childrenr) =>
      if lt_dec d (length keysr) then
        let sep := nth i keys 0 in
        match nth_error children i with
        | Some (BNode keys' children') =>
          let c' := BNode (keys' ++ [sep])
                          (match childrenr with [] => children' |
                                           c :: _ => c :: children' end) in
          BNode (replace i k keys)
                (replace (S i) (BNode keysr (tl childrenr)) (replace i c' children))
        | None => t
        end    
      else tryleft t i
    | _ => tryleft t i
    end end.

  Fixpoint rebalance t path {struct path} :=
    match path with
    | [] => t
    | [i] => rebalance_local t i
    | i :: rest => match t with BNode keys children =>
        match nth_error children i with
        | Some c => match rebalance c rest with BNode keys' children' =>
          let t' := BNode keys (replace i (BNode keys' children') children) in
          if lt_dec (length keys') d then rebalance_local t' i else t' end
        | None => t
        end
    end end.

  Fixpoint delete_at t path :=
    let delete_nth := fix f children i path :=
      match children, i with
      | [], _ => []
      | c :: rest, O => delete_at c path :: rest
      | c :: rest, S i => c :: f rest i path
      end in
    match path with
    | [] => t
    | [i] => let '(t', p') := match t with
             | BNode keys [] => (BNode (remove_at i keys) [],
                                 if le_dec (length keys) d then Some [] else None)
             | BNode keys children =>
                 match nth_error children i with
                 | Some c => let '(c', v, p) := del_max c in
                             (BNode (replace i v keys) (replace i c' children), p)
                 | None => (t, None)
                 end end in
             match p' with Some p' => rebalance t' p' | None => t' end
    | i :: rest => match t with BNode keys children =>
                                BNode keys (delete_nth children i rest) end
    end.
                         
  Definition delete tgt t := option_map (delete_at t) (find_path tgt t).

  Fixpoint contents t :=
    let contents_list := fix f lt lv :=
      match lt, lv with
      | [], _ => lv
      | t :: lt, v :: lv => contents t ++ v :: f lt lv
      | _, _ => []
      end in
    match t with BNode keys children => contents_list children keys end.

  Fixpoint wf_btree_aux t :=
    let wf_btrees := fix f lt :=
      match lt with
      | [] => True
      | t :: rest => wf_btree_aux t /\ f rest
      end in
    match t with BNode keys children =>
      (d <= length keys <= 2 * d)%nat /\
      (children = [] \/ length children = S (length keys) /\ wf_btrees children)
    end.

  Definition wf_btree t := match t with BNode keys children =>
    (length keys <= 2 * d /\ (children = [] \/
                          (2 <= length children /\ length children = S (length keys) /\
                           Forall wf_btree_aux children)))%nat end.

  Definition b_empty := BNode [] [].

  Lemma empty_wf : wf_btree b_empty.
  Proof.
    simpl.
    split; auto; omega.
  Qed.
  
  Lemma insert_length : forall {A} i (x : A) l, length (insert i x l) = S (length l).
  Proof.
    induction i; auto; simpl; intros.
    destruct l; auto; simpl.
    rewrite IHi; auto.
  Qed.

  Fixpoint leaf_path t p {struct p} :=
    match p with
    | [] => match t with BNode keys children => children = [] end
    | i :: rest => match t with BNode keys children =>
      match nth_error children i with
      | Some c => leaf_path c rest
      | None => False
      end end
    end.

  Arguments Nat.div x y : simpl never.
  Arguments skipn A n l : simpl nomatch.
  Arguments firstn A n l : simpl nomatch.
  
  Lemma replace_length : forall {A} i (x : A) l, (i < length l)%nat ->
    length (replace i x l) = length l.
  Proof.
    intros; unfold replace.
    rewrite app_length; simpl.
    rewrite firstn_length, skipn_length.
    rewrite Min.min_l; omega.
  Qed.

  Lemma nth_error_lt : forall {A} n l (x : A), nth_error l n = Some x ->
    (n < length l)%nat.
  Proof.
    intros; apply nth_error_Some; intro X.
    rewrite X in H; discriminate.
  Qed.

  Lemma replace_In : forall {A} l i (x y : A), In y (replace i x l) -> In y l \/ y = x.
  Proof.
    unfold replace; intros.
    rewrite in_app in H; simpl in H.
    destruct H as [? | [? | ?]]; auto; left.
    - eapply firstn_In; eauto.
    - eapply skipn_In; eauto.
  Qed.
  
  Lemma Forall_replace : forall {A} (P : A -> Prop) l i x, Forall P l -> P x ->
    Forall P (replace i x l).
  Proof.
    intros; rewrite Forall_forall in *; intros ? Hin.
    apply replace_In in Hin; destruct Hin; subst; auto.
  Qed.
 
  Lemma replace_In' : forall {A} l i (x y : A), In y (replace i x l) ->
    In y (remove_at i l) \/ y = x.
  Proof.
    unfold replace, remove_at; intros.
    rewrite in_app in *; simpl in H.
    destruct H as [? | [? | ?]]; auto.
  Qed.
  
 Lemma Forall_replace' : forall {A} (P : A -> Prop) l i x, Forall P (remove_at i l) ->
    P x -> Forall P (replace i x l).
  Proof.
    intros; rewrite Forall_forall in *; intros ? Hin.
    apply replace_In' in Hin; destruct Hin; subst; auto.
  Qed.

  Lemma nth_error_replace : forall {A} l i (x : A), (i <= length l)%nat ->
    nth_error (replace i x l) i = Some x.
  Proof.
    intros; unfold replace.
    assert (length (firstn i l) = i) as Hlen.
    { rewrite firstn_length, Min.min_l; auto. }
    rewrite nth_error_app2; rewrite Hlen; auto.
    rewrite minus_diag; auto.
  Qed.      

  Lemma insert_In : forall {A} i l (x y : A), In y (insert i x l) -> In y l \/ y = x.
  Proof.
    induction i; simpl; intros.
    - destruct H; auto.
    - destruct l; simpl in *.
      + destruct H; auto.
      + destruct H; auto.
        specialize (IHi _ _ _ H); destruct IHi; auto.
  Qed.
  
  Lemma Forall_insert : forall {A} (P : A -> Prop) l i x, Forall P l -> P x ->
    Forall P (insert i x l).
  Proof.
    intros; rewrite Forall_forall in *; intros ? Hin.
    apply insert_In in Hin; destruct Hin; subst; auto.
  Qed.

  Fixpoint wf_btree_over t :=
    match t with BNode keys children =>
      (length keys = 2 * d + 1)%nat /\
      (children = [] \/ length children = S (length keys) /\ Forall wf_btree_aux children)
    end.

  Lemma alt_Forall : forall P (lt : list bnode),
    (fix f lt := match lt with [] => True | t :: rest => P t /\ f rest end) lt <->
    Forall P lt.
  Proof.
    induction lt; split; auto.
    - intros (? & ?); constructor; auto.
      rewrite <- IHlt; auto.
    - intro H; inv H; split; auto.
      rewrite IHlt; auto.
  Qed.

  Lemma wf_or_iff : forall keys children,
    (wf_btree_aux (BNode keys children) \/ wf_btree_over (BNode keys children)) <->
    ((d <= length keys <= 2 * d \/ length keys = 2 * d + 1)%nat /\
     (children = [] \/ keys <> [] /\ length children = S (length keys) /\
      Forall wf_btree_aux children)).
  Proof.
    split; intros.
    - destruct H; simpl in H; destruct H as (? & H'); split; auto;
        destruct H' as [|(? & ?)]; auto; right; repeat split; auto;
        try rewrite (alt_Forall wf_btree_aux) in *; auto; intro; subst; simpl in *; omega.
    - destruct H as ([? | ?] & H'); [left | right]; simpl; split; auto;
        destruct H' as [|(Hkeys & ? & ?)]; auto.
      right; split; auto.
      rewrite (alt_Forall wf_btree_aux); auto.
  Qed.
  
  Lemma wf_or_iff' : forall keys children,
    (wf_btree (BNode keys children) \/ wf_btree_over (BNode keys children)) <->
    ((length keys <= 2 * d \/ length keys = 2 * d + 1)%nat /\
     (children = [] \/ keys <> [] /\ length children = S (length keys) /\
      Forall wf_btree_aux children)).
  Proof.
    split; intros.
    - destruct H; simpl in H; destruct H as (? & H'); split; auto;
        destruct H' as [|(? & H')]; try destruct H'; auto; right; repeat split; auto;
        intro; subst; simpl in *; omega.
    - destruct H as ([? | ?] & H'); [left | right]; simpl; split; auto;
        destruct H' as [|(Hkeys & ? & ?)]; auto.
      right; split; auto.
      destruct keys; [contradiction Hkeys; auto | simpl in *; omega].
  Qed.
  
  Lemma odd_div : forall n, (S (2 * n) / 2)%nat = n.
  Proof.
    intro; rewrite <- (NPeano.Nat.add_1_r (2 * n)), Nat.mul_comm, Nat.div_add_l; try omega.
    unfold Nat.div; simpl; omega.
  Qed.

  Lemma Forall_skipn : forall {A} P (l : list A) n, Forall P l -> Forall P (skipn n l).
  Proof.
    intros; rewrite Forall_forall in *; intros ? Hin.
    eapply H, skipn_In; eauto.
  Qed.
  
  Lemma Forall_firstn : forall {A} P (l : list A) n, Forall P l -> Forall P (firstn n l).
  Proof.
    intros; rewrite Forall_forall in *; intros ? Hin.
    eapply H, firstn_In; eauto.
  Qed.

  Lemma insert_nonnil : forall {A} i (x : A) l, insert i x l <> [].
  Proof.
    repeat intro.
    generalize (insert_length i x l); rewrite H; discriminate.
  Qed.
  
  Lemma split_wf : forall keys children i c (Hc : nth_error children i = Some c)
    (Hover : wf_btree_over c) (Hrest : Forall wf_btree_aux (remove_at i children))
    (Hkeys : (d <= length keys <= 2 * d)%nat)
    (Hchildren : length children = S (length keys)),
    wf_btree_aux (split (BNode keys children) i) \/
    wf_btree_over (split (BNode keys children) i).
  Proof.
    intros; unfold split.
    rewrite Hc; destruct c as [keys' children']; rewrite wf_or_iff.
    rewrite insert_length.
    split; [omega | right].
    split; [apply insert_nonnil|].
    generalize (nth_error_lt _ _ _ Hc); intro.
    rewrite insert_length, replace_length; auto.
    rewrite Hchildren; split; auto.
    apply Forall_insert.
    + apply Forall_replace'; auto; simpl.
      repeat rewrite skipn_length.
      destruct Hover as (Hover & Hwf); rewrite Hover.
      rewrite NPeano.Nat.add_1_r, odd_div; simpl.
      split; try omega.
      destruct Hwf as [|(Hlen & ?)]; [subst; rewrite skipn_nil; auto | right].
      rewrite Hlen, Hover.
      split; [omega|].
      rewrite (alt_Forall wf_btree_aux).
      apply Forall_skipn; auto.
    + unfold wf_btree_aux; fold wf_btree_aux.
      rewrite firstn_length, Min.min_l; [|apply Nat.div_le_upper_bound; omega].
      unfold wf_btree_over in Hover.
      destruct Hover as (Hover & Hwf); rewrite Hover.
      rewrite NPeano.Nat.add_1_r, odd_div; simpl.
      split; [omega|].
      destruct Hwf as [|(Hlen & ?)]; [subst; rewrite firstn_nil; auto | right].
      rewrite firstn_length, Hlen, Hover, Min.min_l; [|omega].
      split; auto.
      rewrite (alt_Forall wf_btree_aux).
      apply Forall_firstn; auto.
  Qed.

  Lemma split_wf' : forall keys children i c (Hc : nth_error children i = Some c)
    (Hover : wf_btree_over c) (Hrest : Forall wf_btree_aux (remove_at i children))
    (Hkeys : (length keys <= 2 * d)%nat)
    (Hchildren : length children = S (length keys)),
    wf_btree (split (BNode keys children) i) \/
    wf_btree_over (split (BNode keys children) i).
  Proof.
    intros; unfold split.
    rewrite Hc; destruct c as [keys' children']; rewrite wf_or_iff'.
    rewrite insert_length.
    split; [omega | right].
    split; [apply insert_nonnil|].
    generalize (nth_error_lt _ _ _ Hc); intro.
    rewrite insert_length, replace_length; auto.
    rewrite Hchildren; split; auto.
    apply Forall_insert.
    + apply Forall_replace'; auto; simpl.
      repeat rewrite skipn_length.
      destruct Hover as (Hover & Hwf); rewrite Hover.
      rewrite NPeano.Nat.add_1_r, odd_div; simpl.
      split; try omega.
      destruct Hwf as [|(Hlen & ?)]; [subst; rewrite skipn_nil; auto | right].
      rewrite Hlen, Hover.
      split; [omega|].
      rewrite (alt_Forall wf_btree_aux).
      apply Forall_skipn; auto.
    + unfold wf_btree_aux; fold wf_btree_aux.
      rewrite firstn_length, Min.min_l; [|apply Nat.div_le_upper_bound; omega].
      unfold wf_btree_over in Hover.
      destruct Hover as (Hover & Hwf); rewrite Hover.
      rewrite NPeano.Nat.add_1_r, odd_div; simpl.
      split; [omega|].
      destruct Hwf as [|(Hlen & ?)]; [subst; rewrite firstn_nil; auto | right].
      rewrite firstn_length, Hlen, Hover, Min.min_l; [|omega].
      split; auto.
      rewrite (alt_Forall wf_btree_aux).
      apply Forall_firstn; auto.
  Qed.

  Lemma split_contents : forall t i, contents (split t i) = contents t.
  Proof.
    intros; destruct t; simpl.
    destruct (nth_error children i) eqn: Hi; auto.
    destruct b as [keys' children']; simpl.

  Arguments split parent i : simpl nomatch.
  Arguments removelast A l : simpl nomatch.
  
  Lemma remove_replace : forall {A} i (x : A) l, (i <= length l)%nat ->
    remove_at i (replace i x l) = remove_at i l.
  Proof.
    intros; unfold remove_at, replace.
    assert (length (firstn i l) = i) as Hlen by (rewrite firstn_length, Min.min_l; auto).
    rewrite firstn_app1, firstn_firstn, skipn_app2; auto; rewrite Hlen; auto.
    rewrite <- minus_Sn_m, minus_diag; auto.
  Qed.

  Lemma remove_In : forall {A} (x : A) i l, In x (remove_at i l) -> In x l.
  Proof.
    unfold remove_at; intros.
    rewrite in_app in H; destruct H; [eapply firstn_In | eapply skipn_In]; eauto.
  Qed.
  
  Lemma Forall_remove : forall {A} P i (l : list A), Forall P l ->
    Forall P (remove_at i l).
  Proof.
    intros; rewrite Forall_forall in *; intros ? Hin.
    apply remove_In in Hin; auto.
  Qed.
  
  Lemma insert_at_wf : forall v p t t' (Hinsert : insert_at v t p = Some t')
      (Hwf : wf_btree_aux t) (Hp : leaf_path t (removelast p)),
      wf_btree_aux t' \/ wf_btree_over t'.
  Proof.
    induction p; intros; try discriminate.
    simpl in Hinsert.
    destruct p; [|destruct p].
    - destruct t; inv Hinsert.
      simpl in *; subst.
      destruct Hwf as (Hkeys & _).
      rewrite insert_length.
      destruct (le_dec (S (length keys)) (2 * d)); [left | right]; split; auto; omega.
    - destruct t; simpl in Hp.
      destruct (nth_error children a) as [[keys' [|]]|] eqn: Hc; try discriminate.
      generalize (nth_error_lt _ _ _ Hc); intro.
      generalize (nth_error_In _ _ Hc); intro Hin.
      destruct (lt_dec _ _); inv Hinsert.
      + simpl in *.
        left; destruct Hwf as (? & Hwf); split; auto.
        destruct Hwf as [|(? & Hwf)]; subst.
        { rewrite nth_error_nil in *; discriminate. }
        right.
        rewrite replace_length; auto.
        repeat split; auto.
        rewrite (alt_Forall wf_btree_aux) in *.
        apply Forall_replace; auto; simpl.
        rewrite insert_length; split; auto.
        rewrite Forall_forall in Hwf; specialize (Hwf _ Hin); simpl in Hwf; omega.
      + destruct Hwf as (? & [|(? & Hwf)]);
          [subst; rewrite nth_error_nil in *; discriminate|].
        rewrite (alt_Forall wf_btree_aux) in Hwf.
        eapply split_wf; try apply nth_error_replace; try omega.
        * simpl.
          split; auto; rewrite insert_length.
          rewrite Forall_forall in Hwf; specialize (Hwf _ Hin); simpl in Hwf; omega.
        * rewrite remove_replace; [|omega].
          apply Forall_remove; auto.
        * rewrite replace_length; auto.
    - destruct t.
      destruct (nth_error children a) as [[keys' children']|] eqn: Hc; try discriminate.
      destruct (insert_at _ _ _) eqn: Hinsert'; [|discriminate].
      destruct Hwf as (? & [|(? & Hwf)]);
        [subst; rewrite nth_error_nil in *; discriminate|].
      rewrite (alt_Forall wf_btree_aux) in Hwf.
      pose proof (nth_error_In _ _ Hc) as Hin.
      pose proof (nth_error_lt _ _ _ Hc).
      rewrite Forall_forall in Hwf; pose proof (Hwf _ Hin);
        rewrite <- Forall_forall in Hwf. 
      exploit IHp; eauto.
      { simpl in *.
        rewrite Hc in Hp; auto. }
      destruct b; intros [Hwf' | Hwf'].
      + simpl in Hwf'.
        destruct (le_dec _ _); try omega; inv Hinsert.
        left; simpl; split; auto.
        right; rewrite replace_length; auto; repeat split; auto.
        rewrite (alt_Forall wf_btree_aux) in *.
        apply Forall_replace; auto; simpl.
        destruct Hwf' as (? & Hwf'); split; auto.
        destruct Hwf' as [|(? & Hwf')]; auto; right; split; auto.
        rewrite (alt_Forall wf_btree_aux); auto.
      + simpl in Hwf'.
        destruct (le_dec _ _); try omega; inv Hinsert.
        eapply split_wf; try apply nth_error_replace; try omega; simpl; auto.
        * rewrite remove_replace; [|omega].
          apply Forall_remove; auto.
        * rewrite replace_length; auto.
  Qed.

  Corollary insert_at_wf' : forall v p t t' (Hinsert : insert_at v t p = Some t')
      (Hwf : wf_btree t) (Hp : leaf_path t (removelast p)),
      wf_btree t' \/ wf_btree_over t'.
  Proof.
    destruct p; intros; try discriminate.
    simpl in Hinsert.
    destruct p; [|destruct p].
    - destruct t; inv Hinsert.
      simpl in *; subst.
      destruct Hwf as (Hkeys & _).
      rewrite insert_length.
      destruct (le_dec (S (length keys)) (2 * d)); [left | right]; split; auto; omega.
    - destruct t; simpl in Hp.
      destruct (nth_error children n) as [[keys' [|]]|] eqn: Hc; try discriminate.
      generalize (nth_error_lt _ _ _ Hc); intro.
      generalize (nth_error_In _ _ Hc); intro Hin.
      destruct (lt_dec _ _); inv Hinsert.
      + simpl in *.
        left; destruct Hwf as (? & Hwf); split; auto.
        destruct Hwf as [|(? & ? & Hwf)]; subst.
        { rewrite nth_error_nil in *; discriminate. }
        right.
        rewrite replace_length; auto.
        repeat split; auto.
        apply Forall_replace; auto; simpl.
        rewrite insert_length; split; auto.
        rewrite Forall_forall in Hwf; specialize (Hwf _ Hin); simpl in Hwf; omega.
      + destruct Hwf as (? & [|(? & ? & Hwf)]);
          [subst; rewrite nth_error_nil in *; discriminate|].
        eapply split_wf'; try apply nth_error_replace; try omega.
        * simpl.
          split; auto; rewrite insert_length.
          rewrite Forall_forall in Hwf; specialize (Hwf _ Hin); simpl in Hwf; omega.
        * rewrite remove_replace; [|omega].
          apply Forall_remove; auto.
        * rewrite replace_length; auto.
    - destruct t.
      destruct (nth_error children n) as [[keys' children']|] eqn: Hc; try discriminate.
      destruct (insert_at _ _ _) eqn: Hinsert'; [|discriminate].
      destruct Hwf as (? & [|(? & ? & Hwf)]);
        [subst; rewrite nth_error_nil in *; discriminate|].
      pose proof (nth_error_In _ _ Hc) as Hin.
      pose proof (nth_error_lt _ _ _ Hc).
      rewrite Forall_forall in Hwf; pose proof (Hwf _ Hin);
        rewrite <- Forall_forall in Hwf.
      exploit insert_at_wf; eauto.
      { simpl in *.
        rewrite Hc in Hp; auto. }
      destruct b; intros [Hwf' | Hwf'].
      + simpl in Hwf'.
        destruct (le_dec _ _); try omega; inv Hinsert.
        left; simpl; split; auto.
        right; rewrite replace_length; auto; repeat split; auto.
        rewrite (alt_Forall wf_btree_aux) in *.
        apply Forall_replace; auto; simpl.
        destruct Hwf' as (? & Hwf'); split; auto.
        destruct Hwf' as [|(? & Hwf')]; auto; right; split; auto.
        rewrite (alt_Forall wf_btree_aux); auto.
      + simpl in Hwf'.
        destruct (le_dec _ _); try omega; inv Hinsert.
        eapply split_wf'; try apply nth_error_replace; try omega; simpl; auto.
        * rewrite remove_replace; [|omega].
          apply Forall_remove; auto.
        * rewrite replace_length; auto.
  Qed.

  Lemma find_leaf_aux : forall tgt lt i, (fix f children i :=
    match children with
    | [] => Some []
    | c :: rest => match i with
                   | 0%nat => find_leaf tgt c
                   | S i0 => f rest i0
                   end
    end) lt i = match nth_error lt i with Some c => find_leaf tgt c | None => Some [] end.
  Proof.
    induction lt; intro.
    - rewrite nth_error_nil; auto.
    - destruct i; auto.
      rewrite IHlt; auto.
  Qed.

  Lemma find_leaf_nonnil : forall v t p (Hfind : find_leaf v t = Some p), p <> [].
  Proof.
    induction t using btree_ind; intros.
    simpl in Hfind.
    destruct (find_index v keys) eqn: Hindex; [discriminate|].
    rewrite (find_leaf_aux v children i) in Hfind.
    destruct (nth_error children i) eqn: Hi.
    - destruct (find_leaf v b) eqn: Hfind'; [inv Hfind|]; discriminate.
    - inv Hfind; discriminate.
  Qed.

  Lemma wf_weak : forall t, wf_btree_aux t -> wf_btree t.
  Proof.
    induction t using btree_ind; simpl; intro Haux.
    destruct Haux as (? & Hwf); split; [omega|].
    destruct Hwf as [|(? & ?)]; auto; right; repeat split; try omega.
    rewrite (alt_Forall wf_btree_aux) in *; auto.
  Qed.

  Lemma find_index_le : forall tgt keys i
    (Hfind : find_index tgt keys = NotFound i),
    (i <= length keys)%nat.
  Proof.
    induction keys; simpl; intros.
    - inv Hfind; auto.
    - destruct (Z.ltb tgt a).
      + inv Hfind; omega.
      + destruct (Z.eqb tgt a); [discriminate|].
        destruct (find_index tgt keys) eqn: Hfind'; [discriminate | inv Hfind].
        specialize (IHkeys _ eq_refl); omega.
  Qed.
  
  Corollary find_index_valid : forall tgt keys (children : list bnode) i
    (Hwf : children = [] \/ length children = S (length keys))
    (Hfind : find_index tgt keys = NotFound i),
    (i < length children)%nat \/ children = [].
  Proof.
    intros.
    apply find_index_le in Hfind.
    destruct Hwf; auto; left; omega.
  Qed.

  Lemma nth_error_succeeds : forall {A} n (l : list A) (Hlt : (n < length l)%nat),
      exists x, nth_error l n = Some x.
  Proof.
    induction n; auto; intros; destruct l; simpl in *; try omega; eauto.
    apply IHn; omega.
  Qed.
  
  Lemma find_leaf_path : forall v t p (Hfind : find_leaf v t = Some p)
    (Hwf : wf_btree t),
    leaf_path t (removelast p).
  Proof.
    induction t using btree_ind; intros.
    simpl in Hfind.
    destruct (find_index v keys) eqn: Hindex; [discriminate|].
    rewrite (find_leaf_aux v children i) in Hfind.
    destruct (nth_error children i) eqn: Hi.
    - destruct (find_leaf v b) eqn: Hfind'; [inv Hfind; simpl | discriminate].
      rewrite Forall_forall in H; exploit H; eauto.
      { eapply nth_error_In; eauto. }
      { destruct Hwf as (? & [|(? & ? & Hwf)]);
          [subst; rewrite nth_error_nil in *; discriminate|].
        rewrite Forall_forall in Hwf; eapply wf_weak, Hwf, nth_error_In; eauto. }
      pose proof (find_leaf_nonnil _ _ _ Hfind') as Hnil.
      destruct l; [contradiction Hnil; auto | simpl].
      rewrite Hi; auto.
    - inv Hfind; simpl in *.
      apply find_index_valid with (children := children) in Hindex.
      + destruct Hindex as [Hlt|]; auto.
        apply nth_error_succeeds in Hlt; destruct Hlt; rewrite Hi in *; discriminate.
      + destruct Hwf as (? & [|(? & ? & ?)]); auto.
  Qed.
  
  Lemma insert_wf : forall v t t' (Hinsert : b_insert v t = Some t') (Hwf : wf_btree t),
      wf_btree t'.
  Proof.
    unfold b_insert; intros.
    destruct (find_leaf v t) eqn: Hfind; [|discriminate].
    destruct (insert_at v t l) eqn: Hinsert'; [|discriminate].
    destruct b.
    exploit insert_at_wf'; eauto.
    - eapply find_leaf_path; eauto.
    - unfold wf_btree, wf_btree_over; intros [? | ?]; destruct (le_dec _ _); try omega;
        inv Hinsert; auto.
      split; [simpl; omega|].
      right; repeat split; auto.
      destruct H as (Hover & Hwf'); rewrite Hover.
      rewrite (Nat.add_1_r (2 * d)), odd_div.
      unfold replace; simpl; constructor; [|constructor; auto]; simpl.
      + rewrite firstn_length, Min.min_l; [split|]; try omega.
        destruct Hwf' as [|(? & ?)]; subst; auto; right.
        rewrite firstn_length, Min.min_l; [split; auto | omega].
        rewrite (alt_Forall wf_btree_aux); apply Forall_firstn; auto.
      + repeat rewrite skipn_length; split; [omega|].
        destruct Hwf' as [|(? & ?)]; subst; auto; right.
        split; [omega|].
        rewrite (alt_Forall wf_btree_aux); apply Forall_skipn; auto.
  Qed.

  Lemma insert_In2 : forall {A} i (x : A) l, In x (insert i x l).
  Proof.
    induction i; simpl; auto; intros.
    destruct l; simpl; auto.
  Qed.

  Lemma insert_at_In : forall v t p t' (Hinsert : insert_at v t p = Some t'),
    In v (contents t').
  Proof.
    induction p; simpl; try discriminate; intros.
    destruct p; [|destruct p]; destruct t.
    - inv Hinsert; simpl.
      clear.
      pose proof (insert_In2 a v keys).
      remember (insert a v keys) as lv; clear Heqlv.
      generalize dependent lv; induction children; auto; intros.
      destruct lv; auto.
      rewrite in_app; right; simpl in *.
      destruct H; auto.
    - destruct (nth_error children a) eqn: Ha; [|discriminate].
      destruct b as [keys' children'].
      destruct children'; [|discriminate].
      
  
  Lemma insert_at_sorted : forall v t p (Hp : find_leaf v t = Some p)
    (Hsorted : sorted (contents t)),
    exists t', insert_at v t p = Some t' /\ sorted (contents t').
    
  
  Lemma insert_sorted : forall v t t' (Hinsert : b_insert v t = Some t')
    (Hsorted : sorted (contents t)), sorted (contents t') /\ In v (contents t').
  Proof.
    
  
End BTree.

Definition t_struct_btree := Tstruct _btreeNode noattr.

Fixpoint tree_rep (t : bnode) (p : val) : mpred :=
  let trees_rep := fix f lt lp :=
    match lt, lp with
    | [], [] => emp
    | t :: trest, p :: prest => tree_rep t p * f trest prest
    | _, _ => !! False
    end in
  match t with BNode keys children =>
    if zerop (length keys) then !!(p=nullval) && emp else
      !! (Forall (fun v => Int.min_signed <= v <= Int.max_signed) keys) &&
         EX lp : list val, data_at Tsh t_struct_btree
            (map Vint (map Int.repr keys), (Vint (Int.repr (Zlength keys)), lp)) p *
            trees_rep children lp
  end.


(* Beginning of the API spec for the bin_search.c program *)
Definition search_spec :=
 DECLARE _search
  WITH a: val, sh : share, contents : list Z, tgt : Z, lo : Z, hi : Z
  PRE [ _a OF (tptr tint), _tgt OF tint, _lo OF tint, _hi OF tint ]
            PROP  (readable_share sh; Zlength contents <= Int.max_signed;
                     0 <= lo <= Int.max_signed; Int.min_signed <= hi <= Int.max_signed / 2;
                     hi <= Zlength contents;
                     sorted contents;
                     Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
                     Int.min_signed <= tgt <= Int.max_signed;
                     In tgt contents -> In tgt (sublist lo hi contents))
                  LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
                         temp _lo (Vint (Int.repr lo)); temp _hi (Vint (Int.repr hi)))
          SEP   (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX i:Z,
         PROP (if in_dec Z.eq_dec tgt contents then Znth i contents 0 = tgt else i = -1)
          LOCAL (temp ret_temp  (Vint (Int.repr i)))
           SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs := 
      augment_funspecs prog [search_spec; main_spec].

Lemma sublist_nil1 : forall A i j (l : list A), j <= i -> sublist i j l = [].
Proof.
  intros; destruct (eq_dec i j).
  - subst; apply sublist_nil.
  - unfold sublist; rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma Znth_In : forall A i (l : list A) d x (Hrange : 0 <= i < Zlength l)
                       (Hnth : Znth i l d = x), In x l.
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); [omega|].
  subst; apply nth_In.
  rewrite Zlength_correct in Hrange; auto; Omega0.
Qed.

Lemma In_Znth : forall A (l : list A) x d,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  unfold Znth; intros.
  apply In_nth with (d := d) in H; destruct H as (n & ? & ?).
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; omega.
  - destruct (zlt (Z.of_nat n) 0); [omega|].
    rewrite Nat2Z.id; auto.
Qed.  

Lemma sublist_of_nil : forall A i j, sublist i j (nil : list A) = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_nil, firstn_nil; auto.
Qed.

Fixpoint sorted2 l :=
  match l with
  | [] => True
  | x :: rest => Forall (fun y => x <= y) rest /\ sorted2 rest
  end.

Lemma sorted_equiv : forall l, sorted l <-> sorted2 l.
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct l.
    + simpl; split; auto.
    + rewrite IHl; simpl; split; intros (? & Hall & ?).
      * split; auto; constructor; auto.
        rewrite Forall_forall in *; intros ? Hin.
        specialize (Hall _ Hin); omega.
      * inversion H; subst; auto.
Qed.

Lemma sorted_mono : forall d l i j (Hsort : sorted l) (Hi : 0 <= i <= j)
                           (Hj : j < Zlength l),
    Znth i l d <= Znth j l d.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  destruct (zlt j 0); [omega|].
  revert Hsort.
  generalize dependent j; generalize dependent i; induction l; simpl in *; intros.
  { rewrite Zlength_correct in *; simpl in *; omega. }
  destruct l.
  + rewrite Zlength_correct in *; simpl in *.
    assert (j = 0) by omega.
    assert (i = 0) by omega.
    subst; omega.
  + destruct (eq_dec j 0).
    { assert (i = 0) by omega.
      subst; omega. }
    destruct (Z.to_nat j) eqn: Hnj.
    { contradiction n; apply Z2Nat_inj_0; auto. }
    destruct (eq_dec i 0).
    * subst; simpl.
      destruct Hsort as (? & Hsort).
      destruct n0; try omega.
      rewrite sorted_equiv in Hsort; simpl in Hsort.
      destruct Hsort as (Hsort & _).
      assert (In (nth n0 l d) l) as Hin.
      { apply nth_In.
        assert (S (S n0) < length (a :: z :: l))%nat.
        { rewrite Z2Nat.inj_lt in Hj; try omega.
          rewrite Hnj, Zlength_correct, Nat2Z.id in Hj; auto. }
        simpl in *; omega. }
      rewrite Forall_forall in Hsort; specialize (Hsort _ Hin); omega.
    * destruct (Z.to_nat i) eqn: Hni.
      { contradiction n1; apply Z2Nat_inj_0; auto. }
      assert (Z.of_nat n2 >= 0) as Hi' by omega.
      specialize (IHl _ Hi' (Z.of_nat n0)).
      destruct Hsort.
      repeat rewrite Nat2Z.id in IHl; apply IHl; auto; try omega.
      - split; try omega.
        destruct Hi as (_ & Hi).
        rewrite Z2Nat.inj_le in Hi; omega.
      - rewrite Z2Nat.inj_lt in Hj; try omega.
        rewrite Hnj, Zlength_correct, Nat2Z.id in Hj.
        rewrite Zlength_correct; apply inj_lt; simpl in *; omega.
Qed.

Lemma In_sorted_range : forall d lo hi x l (Hsort : sorted l) (Hlo : 0 <= lo <= hi)
                              (Hhi : hi <= Zlength l)
                              (Hin : In x (sublist lo hi l)),
    Znth lo l d <= x <= Znth (hi - 1) l d.
Proof.
  intros.
  generalize (In_Znth _ _ _ d Hin); intros (i & Hrange & Hi).
  rewrite Zlength_sublist in Hrange; auto.
  rewrite Znth_sublist in Hi; auto; try omega.
  subst; split; apply sorted_mono; auto; omega.
Qed.

Lemma In_sorted_gt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l 0 = n)
                            (Hgt : n < x),
    In x (sublist (i + 1) hi l).
Proof.
  intros.
  rewrite sublist_split with (mid := i + 1) in Hin; try omega.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range 0 lo (i + 1) x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | omega]).
  replace (i + 1 - 1) with i in X by omega.
  specialize (X H); subst; omega.
Qed.

Lemma In_sorted_lt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l 0 = n)
                            (Hgt : x < n),
    In x (sublist lo i l).
Proof.
  intros.
  rewrite sublist_split with (mid := i) in Hin; try omega.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range 0 i hi x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | omega]).
  specialize (X H); subst; omega.
Qed.

Definition while_Inv contents tgt sh a := EX lo : Z, EX hi : Z,
    PROP  (readable_share sh; Zlength contents <= Int.max_signed;
           0 <= lo <= Int.max_signed; Int.min_signed <= hi <= Int.max_signed / 2;
           hi <= Zlength contents;
           In tgt contents -> In tgt (sublist lo hi contents))
    LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
           temp _lo (Vint (Int.repr lo)); temp _hi (Vint (Int.repr hi)))
    SEP   (data_at sh (tarray tint (Zlength contents))
                   (map Vint (map Int.repr contents)) a).

Definition while_Inv' contents tgt sh a := EX lo : Z, EX hi : Z,
    PROP  (readable_share sh; Zlength contents <= Int.max_signed;
           0 <= lo < hi; Int.min_signed <= hi <= Int.max_signed / 2;
           hi <= Zlength contents;
           In tgt contents -> In tgt (sublist lo hi contents))
    LOCAL (temp _a a; temp _tgt (Vint (Int.repr tgt));
           temp _lo (Vint (Int.repr lo)); temp _hi (Vint (Int.repr hi)))
    SEP   (data_at sh (tarray tint (Zlength contents))
                   (map Vint (map Int.repr contents)) a).

Lemma body_search: semax_body Vprog Gprog f_search search_spec.
Proof.
  start_function.
  generalize (Int.min_signed_neg); intro.
  forward_while (while_Inv contents tgt sh a).
  { entailer!.
    Exists lo; Exists hi; entailer!. }
  { entailer!. }
  forward.
  rewrite Int.shr_div_two_p, Int.add_signed.
  repeat rewrite Int.signed_repr; try omega.
  rewrite Int.unsigned_repr; try computable; simpl.
  unfold two_power_pos; simpl.
  remember ((lo0 + hi0) / 2) as mid.
  assert (0 <= mid < Zlength (map Int.repr contents)).
  { subst; split; [apply Z_div_pos; omega|].
    rewrite Zlength_map.
    apply Zdiv_lt_upper_bound; omega. }
  assert (0 <= mid < Zlength contents) by (rewrite Zlength_map in *; auto).
  assert (lo0 <= (lo0 + hi0) / 2 < hi0).
  { split; [apply Zdiv_le_lower_bound | apply Zdiv_lt_upper_bound]; omega. }
  forward.
  { entailer!.
    rewrite Znth_map with (d' := Int.repr 0); simpl; auto. }
  rewrite Znth_map with (d' := Int.repr 0); auto.
  rewrite Znth_map with (d' := 0); auto.
  exploit Znth_In; eauto.
  instantiate (1 := 0); intro Hin.
  match goal with H : Forall _ _ |- _ =>
                  rewrite Forall_forall in H; specialize (H _ Hin) end.
  forward_if (while_Inv contents tgt sh a); try forward.
  - Exists ((lo0 + hi0) / 2); entailer!.
    destruct (in_dec _ _ _); auto.
    subst; contradiction n; auto.
  - forward_if (while_Inv contents tgt sh a); try forward.
    + Exists (mid + 1) hi0; entailer!.
      eapply In_sorted_gt; eauto; omega.
    + Exists lo0 mid; entailer!.
      eapply In_sorted_lt; eauto; omega.
    + unfold PROPx, LOCALx, SEPx, local, lift1; simpl; entailer!.
      unfold overridePost; destruct (eq_dec ek EK_normal); auto.
      subst; simpl; normalize.
      unfold POSTCONDITION, abbreviate; simpl.
      normalize.
  - unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift; simpl; entailer!.
    unfold overridePost; destruct (eq_dec ek EK_normal); auto.
    subst; simpl; normalize.
    unfold while_Inv.
    (* For some reason, Intro doesn't work here. *)
    refine (exp_left _ _ _); intro lo1.
    refine (exp_left _ _ _); intro hi1.
    Exists (lo1, hi1).
    normalize.
  - split; try omega.
    etransitivity; [apply (Zplus_le_compat_l _ (Int.max_signed / 2)); omega|].
    etransitivity; [apply (Zplus_le_compat_r _ (Int.max_signed / 2)); omega|].
    rewrite Zplus_diag_eq_mult_2, Z.mul_comm.
    apply Z_mult_div_ge; omega.
  - forward.
    Exists (-1); entailer!.
    destruct (in_dec _ _ _); auto.
    match goal with H : context[sublist lo0 hi0 _] |- _ => rewrite sublist_nil1 in H end;
      try omega.
    simpl in *; contradiction.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name four _four.
  start_function.
  forward_call (four,Ews,four_contents,3,0,4).
  { split; auto; simpl.
    repeat split; try omega; try computable.
    * unfold four_contents, Zlength; simpl; computable.
    * unfold four_contents, Zlength; simpl; computable.
    * repeat constructor; computable. }
  Intro r; forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_cons body_search.
semax_func_cons body_main.
Qed.
