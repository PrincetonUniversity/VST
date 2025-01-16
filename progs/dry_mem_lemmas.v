Require Import VST.veric.juicy_mem.
Require Import VST.veric.initial_world.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.mem_lessdef.
Require Import VST.floyd.proofauto.

(* functions on byte arrays and CompCert mems *)
Lemma drop_alloc m : { m' | (let (m1, b) := Mem.alloc m 0 1 in Mem.drop_perm m1 b 0 1 Nonempty) = Some m' }.
Proof.
  destruct (Mem.alloc m 0 1) eqn: Halloc.
  apply Mem.range_perm_drop_2.
  intro; eapply Mem.perm_alloc_2; eauto.
Qed.

Definition store_byte_list m b ofs lv :=
  Mem.storebytes m b ofs (concat (map (encode_val Mint8unsigned) lv)).

Lemma access_at_readable : forall m b o sh (Hsh : readable_share sh),
  access_at m (b, o) Cur = perm_of_sh sh ->
  Mem.perm m b o Cur Readable.
Proof.
  unfold access_at, perm_of_sh, Mem.perm; intros.
  simpl in H; rewrite H.
  if_tac; if_tac; constructor || contradiction.
Qed.

Lemma access_at_writable : forall m b o sh (Hsh : writable_share sh),
  access_at m (b, o) Cur = perm_of_sh sh ->
  Mem.perm m b o Cur Writable.
Proof.
  unfold access_at, perm_of_sh, Mem.perm; intros.
  simpl in H; rewrite H.
  apply writable_writable0 in Hsh.
  if_tac; if_tac; constructor || contradiction.
Qed.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Lemma has_ext_state : forall m (z z' : OK_ty),
  state_interp m z ∗ <absorb> has_ext z' ⊢ ⌜z = z'⌝.
Proof.
  intros.
  iIntros "((_ & Hz) & >Hz')".
  iDestruct (own_valid_2 with "Hz Hz'") as %?%@excl_auth_agree; done.
Qed.

Lemma change_ext_state : forall m (z z' : OK_ty),
  state_interp m z ∗ has_ext z ⊢ |==> state_interp m z' ∗ has_ext z'.
Proof.
  intros.
  iIntros "(($ & Hz) & Hext)".
  iMod (own_update_2 with "Hz Hext") as "($ & $)"; last done.
  apply @excl_auth_update.
Qed.

Lemma memory_block_writable_perm : forall sh n b ofs m z, writable_share sh ->
  (0 <= ofs)%Z -> (Z.of_nat n + ofs < Ptrofs.modulus)%Z ->
  state_interp m z ∗ <absorb> memory_block' sh n b ofs ⊢
  ⌜Mem.range_perm m b ofs (ofs + Z.of_nat n) Memtype.Cur Memtype.Writable⌝.
Proof.
  intros.
  iIntros "((Hm & _) & >Hb)".
  rewrite memory_block'_eq // /memory_block'_alt if_true; last auto.
  destruct (eq_dec sh Share.top); first subst;
    (iDestruct (VALspec_range_perm with "[$]") as %?; [by apply perm_of_freeable || by apply perm_of_writable|]);
    simpl in *; iPureIntro; first eapply Mem.range_perm_implies; try done.
  constructor.
Qed.

Local Transparent memory_block.

Lemma data_at__writable_perm : forall {cs : compspecs} sh t p m z, writable_share sh ->
  state_interp m z ∗ <absorb> data_at_ sh t p ⊢
  ⌜exists b ofs, p = Vptr b ofs /\
    Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof t) Memtype.Cur Memtype.Writable⌝.
Proof.
  intros.
  rewrite data_at__memory_block.
  iIntros "(Hm & >((% & %) & Hp))".
  destruct p; try contradiction.
  iExists _, _; iSplit; first done.
  iDestruct "Hp" as "(% & Hp)".
  iDestruct (memory_block_writable_perm with "[$Hm $Hp]") as %Hperm; [done | rep_lia..|].
  rewrite Z2Nat.id in Hperm; auto.
  pose proof (sizeof_pos t); lia.
Qed.

Lemma data_at_bytes : forall {CS : compspecs} sh z (bytes : list val) buf m o
  (Hreadable : readable_share sh) (Hlen : z = Zlength bytes)
  (Hdef : Forall (fun x => x <> Vundef) bytes),
  state_interp m o ∗ <absorb> data_at sh (tarray tuchar z) bytes buf ⊢
  ⌜match buf with
   | Vptr b ofs =>
       Mem.loadbytes m b (Ptrofs.unsigned ofs) z =
         Some (concat (map (encode_val Mint8unsigned) bytes))
   | _ => False
   end⌝.
Proof.
  intros.
  assert_PROP (field_compatible (tarray tuchar z) [] buf).
  { unfold data_at, field_at; iIntros "(_ & >($ & _))". }
  destruct buf; try by destruct H.
  remember (Z.to_nat z) as n; generalize dependent i; generalize dependent bytes; generalize dependent z; induction n; intros.
  { assert (z = 0) as -> by rep_lia.
    destruct bytes; last by autorewrite with sublist in *; rep_lia.
    rewrite Mem.loadbytes_empty //; auto. }
  rewrite (split2_data_at_Tarray_tuchar _ _ 1) // /=; last lia.
  iIntros "(Hz & >(H & Hrest))".
  destruct bytes; first by autorewrite with sublist in *; rep_lia.
  inversion Hdef; clear Hdef.
  autorewrite with sublist in Hlen.
  rewrite /field_address0 if_true /=.
  2: { rewrite field_compatible0_cons; split; auto; lia. }
  rewrite sublist_1_cons (sublist_same _ (z - 1)) //; last lia.
  iAssert ⌜field_compatible (tarray tuchar (z - 1)) [] (Vptr b (Ptrofs.add i (Ptrofs.repr 1)))⌝ with "[Hrest]" as %?.
  { unfold data_at, field_at; iDestruct "Hrest" as "($ & _)". }
  iDestruct (IHn with "[$Hz $Hrest]") as %Hrest; [lia || done..|].
  iDestruct "Hz" as "(Hm & _)".
  rewrite sublist_0_cons // sublist_nil data_at_tuchar_singleton_array_inv.
  iAssert ⌜field_compatible tuchar [] (Vptr b i)⌝ with "[H]" as %?.
  { unfold data_at, field_at; iDestruct "H" as "($ & _)". }
  erewrite <-mapsto_data_at', mapsto_core_load by done.
  iDestruct (core_load_load' with "[$Hm $H]") as %Hbyte.
  apply Mem.load_loadbytes in Hbyte as (byte & Hbyte & ->); subst.
  rewrite Ptrofs.add_unsigned !Ptrofs.unsigned_repr // in Hrest.
  2: { destruct H as (? & ? & ? & ?); simpl in *; rep_lia. }
  eapply Mem.loadbytes_concat in Hrest; eauto; [|lia..].
  pose proof (Mem.loadbytes_length _ _ _ _ _ Hbyte) as Hlen; simpl in Hlen.
  destruct byte as [|byte []]; [done | | done].
  replace (encode_val _ (decode_val _ [byte])) with [byte].
  replace (1 + (Z.succ (Zlength bytes) - 1)) with (Z.succ (Zlength bytes)) in Hrest by lia; done.
  { destruct byte; try done.
    rewrite decode_byte_val zero_ext_inrange /= Int.unsigned_repr; [|rep_lia..].
    rewrite /encode_int /= Byte.repr_unsigned rev_if_be_singleton //. }
Qed.

(* up *)
Lemma perm_order_antisym' : forall p p', perm_order p p' -> perm_order p' p -> p = p'.
Proof.
  inversion 1; auto; inversion 1; auto.
Qed.

Lemma mem_equiv_access : forall m m', mem_equiv m m' -> access_at m = access_at m'.
Proof.
  intros ?? (_ & Hperm & _).
  unfold Mem.perm in Hperm.
  extensionality l.
  destruct l as (b, o).
  extensionality k.
  apply equal_f with b, equal_f with o, equal_f with k in Hperm.
  unfold access_at; simpl.
  destruct (_ !!! _).
  - pose proof (equal_f Hperm p) as Hp; simpl in *.
    pose proof (perm_refl p) as Hrefl; rewrite Hp in Hrefl.
    destruct (_ !!! _); [simpl in * | contradiction].
    f_equal; apply perm_order_antisym'; auto.
    apply equal_f with p0 in Hperm.
    rewrite Hperm; apply perm_refl.
  - destruct (_ !!! _); auto.
    apply equal_f with p in Hperm; simpl in Hperm.
    pose proof (perm_refl p) as Hrefl; rewrite <- Hperm in Hrefl; contradiction.
Qed.

Lemma mem_equiv_contents : forall m m' b o (Heq : mem_equiv m m')
  (Hreadable : Mem.perm m b o Cur Readable),
  contents_at m (b, o) = contents_at m' (b, o).
Proof.
  intros ???? (Hload & Hperm & _) ?.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in Hload.
  Opaque Mem.loadbytes.
  apply equal_f with b, equal_f with o, equal_f with 1 in Hload.
  unfold contents_at; simpl.
  rewrite !if_true in Hload.
  inv Hload; auto.
  { unfold Mem.range_perm.
    intros; assert (ofs = o) by lia; subst.
    rewrite <- Hperm; auto. }
  { unfold Mem.range_perm.
    intros; assert (ofs = o) by lia; subst; auto. }
Qed.

Lemma mem_auth_equiv : forall m m' (Heq : mem_equiv m m'), mem_auth m ⊢ mem_auth m'.
Proof.
  intros.
  rewrite /mem_auth.
  apply bi.exist_mono; intros σ.
  iIntros "(%Hcoh & $)"; iPureIntro; split; last done.
  unfold coherent in *.
  intros loc; specialize (Hcoh loc).
  unfold coherent_loc, contents_cohere, access_cohere in *;
    destruct Hcoh as (Hnext & Hcontents & Haccess); split3.
  - destruct Heq as (_ & _ & <-); done.
  - intros.
    destruct loc as (b, o); erewrite <- mem_equiv_contents; eauto.
    rewrite /resource_at /resR_to_resource in H Haccess.
    destruct (σ !! (b, o))%stdpp eqn: Hloc; rewrite Hloc // /= in H Haccess.
    destruct s; inv H.
    simpl in *.
    destruct dq as [[]|]; try done; rewrite H1 /= in Haccess.
    + rewrite perm_access.
      eapply perm_order''_trans; eauto.
      by apply perm_of_readable_share.
    + if_tac in Haccess; try done.
      rewrite perm_access.
      eapply perm_order''_trans; eauto.
  - erewrite <- mem_equiv_access; eauto.
Qed.

Lemma storebytes_nil : forall m b o m', Mem.storebytes m b o [] = Some m' ->
  mem_equiv m m'.
Proof.
  intros; split3.
  - by symmetry; do 3 extensionality; eapply mem_lemmas.loadbytes_storebytes_nil.
  - rewrite /Mem.perm.
    by do 4 extensionality; erewrite <- Mem.storebytes_access.
  - by erewrite <- Mem.nextblock_storebytes.
Qed.

Lemma data_at__storebytes : forall {CS : compspecs} m m' sh z b o lv (Hsh : writable_share sh)
  (Hty : Forall (tc_val' tuchar) lv)
  (Hstore : Mem.storebytes m b (Ptrofs.unsigned o) (concat (map (encode_val Mint8unsigned) lv)) = Some m')
  (Hz : z = Zlength lv),
  mem_auth m ∗ data_at_ sh (tarray tuchar z) (Vptr b o) ⊢ |==>
  mem_auth m' ∗ data_at sh (tarray tuchar z) lv (Vptr b o).
Proof.
  intros.
  remember (Z.to_nat z) as n; generalize dependent o; generalize dependent lv; generalize dependent z; generalize dependent m; induction n; intros; subst.
  { destruct lv; try done; simpl in *.
    rewrite mem_auth_equiv; last by eapply storebytes_nil.
    rewrite data_at__Tarray Zlength_nil Zrepeat_0; auto.
    { rewrite Zlength_cons in Heqn; rep_lia. } }
  assert_PROP (field_compatible (tarray tuchar (Zlength lv)) [] (Vptr b o)) by entailer!.
  rewrite (split2_data_at__Tarray_tuchar _ _ 1) // /=; last lia.
  iIntros "(Hm & H & Hrest)".
  rewrite /field_address0 if_true /=.
  2: { rewrite field_compatible0_cons; split; auto; lia. }
  destruct lv; first done; simpl in *.
  apply Mem.storebytes_split in Hstore as (? & Hstore1 & Hstore2).
  apply Mem.storebytes_store in Hstore1; last by apply Z.divide_1_l.
  rewrite data_at__eq data_at_tuchar_singleton_array_inv /=.
  iAssert ⌜field_compatible tuchar [] (Vptr b o)⌝ with "[H]" as %?.
  { unfold data_at, field_at; iDestruct "H" as "($ & _)". }
  erewrite <- mapsto_data_at' by done.
  inv Hty.
  iMod (lifting.mapsto_store with "[$Hm $H]") as "(Hm & H)"; [eauto..|].
  rewrite encode_val_length /= in Hstore2.
  rewrite /Ptrofs.add Ptrofs.unsigned_repr //.
  rewrite -> Zlength_cons in *.
  iMod (IHn with "[$Hm $Hrest]") as "($ & Hrest)"; [lia || done..| |].
  { rewrite Ptrofs.unsigned_repr //.
    destruct H as (_ & _ & H & _); simpl in H; rep_lia. }
  rewrite (split2_data_at_Tarray_tuchar _ (Z.succ (Zlength lv)) 1) // /=; try lia.
  2: { apply Zlength_cons. }
  rewrite sublist_0_cons // sublist_nil sublist_1_cons sublist_same //; last lia.
  rewrite -data_at_tuchar_singleton_array.
  erewrite mapsto_data_at' by done.
  rewrite /field_address0 if_true /=.
  by iFrame.
  { rewrite field_compatible0_cons; split; auto; lia. }
Qed.

Lemma encode_vals_length : forall lv,
  length (concat (map (encode_val Mint8unsigned) lv)) = length lv.
Proof.
  induction lv; auto; simpl.
  rewrite app_length IHlv encode_val_length //.
Qed.

Definition main_pre_dry (m : mem) (prog : Clight.program) (ora : OK_ty)
  (ts : list Type) (gv : globals) (z : OK_ty) :=
  Genv.globals_initialized (Genv.globalenv prog) (Genv.globalenv prog) m /\ z = ora.

Definition main_post_dry (m0 m : mem) (prog : Clight.program) (ora : OK_ty)
  (ts : list Type) (gv : globals) (z : OK_ty) : Prop := True. (* the desired postcondition might vary by program *)

(* simulate funspec2pre/post *)

(*Definition main_pre_juicy {Z} prog (ora : Z) gv (x' : rmap * {ts : list Type & unit})
  (ge_s: extspec.injective_PTree block) args (z : Z) (m : juicy_mem) :=
    Val.has_type_list args [] /\
(*    (exists phi0 phi1 : rmap,
       join phi0 phi1 (m_phi m) /\*)
       (app_pred (main_pre prog ora gv
          (filter_genv (semax_ext.symb2genv ge_s), nil))
         (m_phi m) (*phi0 /\
       necR (fst x') phi1*) /\ joins (ghost_of (m_phi m)) [Some (ext_ref z, NoneP)]).

Definition xtype_of_option_typ (t: option typ) : xtype :=
match t with Some t => inj_type t | None => Xvoid end.


Definition main_post_juicy {Z} prog (ora : Z) gv (x' : rmap * {ts : list Type & unit})
  (ge_s: extspec.injective_PTree block) (tret : option typ) ret (z : Z) (m : juicy_mem) :=
  (*exists phi0 phi1 : rmap,
       join phi0 phi1 (m_phi m) /\*)
       (app_pred (main_post prog gv
          (semax.make_ext_rval (filter_genv (semax_ext.symb2genv ge_s)) (xtype_of_option_typ tret) ret))
         (m_phi m)(*phi0 /\
       necR (fst x') phi1*) /\ joins (ghost_of (m_phi m)) [Some (ext_ref z, NoneP)]).

Lemma main_dry : forall {Z} prog (ora : Z) ts gv,
  (forall t b vl x jm,
  Genv.init_mem (program_of_program prog) = Some (m_dry jm) ->
  main_pre_juicy prog ora gv t b vl x jm ->
  main_pre_dry (m_dry jm) prog ora ts gv x) /\
  (forall t b ot v x jm0 jm,
    (exists vl x0, main_pre_juicy prog ora gv t b vl x0 jm0) ->
    (level jm <= level jm0)%nat ->
    resource_at (m_phi jm) = resource_fmap (approx (level jm)) (approx (level jm)) oo juicy_mem_lemmas.rebuild_juicy_mem_fmap jm0 (m_dry jm) ->
    ghost_of (m_phi jm) = Some (ghost_PCM.ext_ghost x, compcert_rmaps.RML.R.NoneP) :: ghost_fmap (approx (level jm)) (approx (level jm)) (tl (ghost_of (m_phi jm0))) ->
    (main_post_dry (m_dry jm0) (m_dry jm) prog ora ts gv x ->
     main_post_juicy prog ora gv t b ot v x jm)).
Proof.
  split; intros.
  - unfold main_pre_juicy, main_pre_dry in *.
    destruct H0 as (? & Hpre & Hext).
    unfold main_pre in Hpre.
    destruct Hpre as (? & ? & J & Hglobals & Htrace).
    split.
    + apply Genv.init_mem_characterization_gen; auto.
    + symmetry; eapply has_ext_compat; eauto.
      eexists; eauto.
  - unfold main_post_juicy.
    split; [apply I|].
    rewrite H2.
    eexists; constructor; constructor.
    instantiate (1 := (_, _)); constructor; simpl; [|constructor; auto].
    apply ext_ref_join.
Qed.*)

End mpred.
