Require Import compcert.common.Values.
Require Import msl.eq_dec.
Require Import List.
Require Import Omega.

Definition Time := nat.
Parameter (Loc : Type) (L_eq : EqDec Loc).
Definition Val := val.
Definition Event := (Loc * Val * Time)%type.
Definition View := Loc -> option Time.
Definition Msg := (Event * View)%type.
Parameters (ThreadId : Type) (T_eq : EqDec ThreadId).
Definition State := (list Msg * (ThreadId -> option View) * View)%type.

Inductive Op := Read_NA (l : Loc) (v : Val) | Read_A (l : Loc) (v : Val)
              | Write_NA (l : Loc) (v : Val) | Write_R (l : Loc) (v : Val).

Definition upd {A B} {A_eq : EqDec A} (f : A -> option B) a b c := if eq_dec c a then Some b else f c.

Definition join (V1 V2 : View) l := match V1 l, V2 l with
| Some a, Some b => Some (max a b)
| Some a, _ | _, Some a => Some a
| None, None => None end.

Definition option_le t1 t2 := match t1, t2 with
| Some a, Some b => a <= b
| None, _ => True
| _, None => False end.

Definition option_lt t1 t2 := match t1, t2 with
| Some a, Some b => a < b
| None, _ => True
| _, None => False end.

Inductive step : State -> Op -> ThreadId -> State -> Prop :=
| sRead_A M T N l v t p V Vt (HM : In ((l, v, t), V) M) (Hp : T p = Some Vt) (Ht : option_le (Vt l) (Some t)) :
    step (M, T, N) (Read_A l v) p (M, upd T p (join Vt V), N)
| sRead_NA M T N l v t p V Vt (HM : In ((l, v, t), V) M) (Hp : T p = Some Vt) (Ht : option_le (Vt l) (Some t))
    (Hlast : forall v' t' V', In ((l, v', t'), V') M -> option_le (Some t') (Vt l)) :
    step (M, T, N) (Read_NA l v) p (M, upd T p (join Vt V), N)
| sWrite_R M T N l v t p Vt V' (HM : ~exists v' V, In ((l, v', t), V) M) (Hp : T p = Some Vt)
    (HN : option_le (N l) (Vt l))
    (Ht : option_lt (Vt l) (Some t)) (HV' : V' = upd Vt l t) :
    step (M, T, N) (Write_R l v) p (((l, v, t), V') :: M, upd T p V', N)
| sWrite_NA M T N l v t p Vt V' (HM : ~exists v' V, In ((l, v', t), V) M) (Hp : T p = Some Vt)
    (HN : option_le (N l) (Vt l))
    (HV' : V' = upd Vt l t) (Ht : forall v' t' V, In ((l, v', t'), V) M -> t' < t) :
    step (M, T, N) (Write_NA l v) p (((l, v, t), V') :: M, upd T p V', N).

Lemma remove_old_NA_write : forall M1 M2 T N l v t V v' t' V' op p M1' M2' T' N'
  (Hop : match op with Read_NA _ _ | Write_NA _ _ => True | _ => False end)
  (Hin : In ((l, v', t'), V') (M1 ++ M2)) (Hnew : t < t'),
  step (M1 ++ ((l, v, t), V) :: M2, T, N) op p (M1' ++ ((l, v, t), V) :: M2', T', N') <->
  step (M1 ++ M2, T, N) op p (M1' ++ M2', T', N').
Proof.
  split; intros; inversion H; subst; try contradiction.
  - assert (M1 = M1' /\ M2 = M2') as [] by admit; subst.
    econstructor; eauto.
    { rewrite in_app_iff in *; destruct HM as [|[X|]]; auto; inversion X; subst.
      lapply (Hlast v' t' V').
      destruct (Vt l0); simpl in *; [omega | contradiction].
      { rewrite in_app_iff; simpl; tauto. } }
    intros ??? Hin'; eapply Hlast.
    rewrite in_app_iff in *; simpl; destruct Hin'; eauto.
  - destruct M1'; inversion H6; subst.
    { contradiction HM.
      do 2 eexists; rewrite in_app_iff; simpl; eauto. }
    assert (M1 = M1' /\ M2 = M2') as [] by admit; subst.
    simpl; econstructor; eauto.
    { intros (? & ? & Hin'); contradiction HM.
      do 2 eexists; rewrite in_app_iff in *; simpl; destruct Hin'; eauto. }
    intros ??? Hin'; eapply Ht.
    rewrite in_app_iff in *; simpl; destruct Hin'; eauto.
  - assert (M1 = M1' /\ M2 = M2') as [] by admit; subst.
    econstructor; eauto.
    { rewrite in_app_iff in *; simpl; tauto. }
    intros ??? Hin'.
    rewrite in_app_iff in Hin'; destruct Hin' as [|[X|]]; try solve [eapply Hlast; rewrite in_app_iff; eauto].
    inversion X; subst.
    specialize (Hlast _ _ _ Hin).
    destruct (Vt l0); try contradiction; simpl in *; omega.
  - destruct M1'; [admit | inversion H6; subst].
    assert (M1 = M1' /\ M2 = M2') as [] by admit; subst.
    simpl; econstructor; eauto.
    { intros (? & ? & Hin'); contradiction HM.
      rewrite in_app_iff in Hin'; destruct Hin' as [|[X|]]; try solve [do 2 eexists; rewrite in_app_iff; eauto].
      inversion X; subst.
      specialize (Ht _ _ _ Hin); omega. }
    intros ??? Hin'.
    rewrite in_app_iff in Hin'; destruct Hin' as [|[X|]]; try solve [eapply Ht; rewrite in_app_iff; eauto].
    inversion X; subst.
    specialize (Ht _ _ _ Hin); omega.
Admitted.

(* If each location is dedicated to either atomic or nonatomic:
   * We only need to store the latest value at each nonatomic location; permissions take care of the timestamp
   constraints.
   * We can do without N, and any entries for nonatomic locations in T. This also means we don't need to change
   T on nonatomic writes.
   * Atomic reads/writes must both transfer permissions and process messages. Views should contain permissions
   rather than timestamps for nonatomic locations.
   * We can factor M by location and use it as the memory (atomic locations contain sets of value-timestamp-view
   tuples). Each thread's local view includes permissions for nonatomics and timestamps for atomics. There
   might be some oracle involved, but the coherence should be the usual, with possibly some permissions removed
   from a view in memory when a thread reads from it. *)
(* In a single-writer protocol, the writer assertion is in fact an assertion on the objective latest write to the
   location, rather than the thread's current view.
   How does iGPS's protocol model collapse if protocols are always single-writer?
   It seems like the writer assertion can safely be made viewless, since it will likewise always have the latest
   write to the location.
   Reader assertions still need views, though. *)