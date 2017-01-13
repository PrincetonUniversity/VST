Require Import sepcomp.core_semantics.
Require Import sepcomp.rg_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.linking.
Require Import sepcomp.linking_simulations.
Require Import sepcomp.linking_proof.
Require Import sepcomp.Coqlib2.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require compcert.cfrontend.Ctypes.
Require compcert.cfrontend.Clight.

Set Implicit Arguments.

Definition is_defchar (mv: memval) :=
  match mv with
    | Byte _ => True
    | _ => False
  end.

Inductive extcall_storebytes_sem
  (F V: Type) (ge: Genv.t F V): list memval -> list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_storebytes_sem_intro: forall (b: block) (ofs: int) bytes m m',
      Zlength bytes > 0 ->
      Forall is_defchar bytes ->
      Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
      extcall_storebytes_sem ge bytes (Vptr b ofs :: nil) m E0 Vundef m'.

Lemma extcall_storebytes_sem_inject_comm:
  forall (F V : Type) (ge : Genv.t F V) (vargs : list val)
     (m1 : mem) (t : trace) (m2 : mem)
     (f : block -> option (block * Z)) (m1' : mem)
     (vargs' : list val) bytes,
   meminj_preserves_globals ge f ->
   extcall_storebytes_sem ge bytes vargs m1 t Vundef m2 ->
   Mem.inject f m1 m1' ->
   val_list_inject f vargs vargs' ->
   exists (m2' : mem),
     extcall_storebytes_sem ge bytes vargs' m1' t Vundef m2' /\
     Mem.inject f m2 m2' /\
     Mem.unchanged_on (loc_unmapped f) m1 m2 /\
     Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros. inv H0. inv H2. inv H9. inv H7.
  assert (RPDST: Mem.range_perm m1 b (Int.unsigned ofs)
                 (Int.unsigned ofs + Z_of_nat (length bytes)) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. solve[auto with mem].
  assert (PDST: Mem.perm m1 b (Int.unsigned ofs) Cur Nonempty).
    apply RPDST. rewrite Zlength_correct in H3. omega.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.storebytes_mapped_inject; eauto.
  instantiate (1 := bytes).
  clear - H4.
  induction bytes.
  constructor.
  constructor. destruct a. inv H4. simpl in H1. elimtype False; auto.
  constructor.
  inv H4. simpl in H1. elimtype False; auto.
  inv H4.
  solve[eapply IHbytes; auto].
  intros [m2' [C D]].
  exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto.
  split; auto.
  split; auto.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  rewrite H6; intros x; congruence.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
  eelim H2; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  instantiate (1 := bytes).
  omega.
  instantiate (1 := memval_inject f).
  clear - H4.
  induction bytes.
  constructor.
  constructor. destruct a. inv H4. simpl in H1. elimtype False; auto.
  constructor.
  inv H4. simpl in H1. elimtype False; auto.
  solve[inv H4; auto].
Qed.

Lemma storebytes_sem_inject_comm:
  forall F V (ge: Genv.t F V) m1 m1' m2 bytes b ofs j b' delta,
   Mem.storebytes m1 b (Int.unsigned ofs) bytes = Some m1' ->
   Zlength bytes > 0 ->
   Forall is_defchar bytes ->
   meminj_preserves_globals ge j ->
   Mem.inject j m1 m2 ->
   j b = Some (b', delta) ->
   exists m2',
     Mem.storebytes m2 b' (Int.unsigned (Int.add ofs (Int.repr delta))) bytes = Some m2' /\
     Mem.inject j m1' m2' /\
     Mem.unchanged_on (loc_unmapped j) m1 m1' /\
     Mem.unchanged_on (loc_out_of_reach j m1) m2 m2'.
Proof.
intros.
edestruct extcall_storebytes_sem_inject_comm
 with (vargs := Vptr b (Int.repr (Int.unsigned ofs)) :: nil); eauto.
eapply extcall_storebytes_sem_intro; eauto.
rewrite Int.repr_unsigned.
solve[eauto].
destruct H5 as [? [? [? ?]]].
exists x.
split; auto.
inv H5.
auto.
rewrite Int.repr_unsigned in H15.
auto.
Qed.

(*Definition genv := Genv.t Clight.fundef Ctypes.type.*)

Inductive fmode: Type := RDONLY | WRONLY | RDWR.

Definition fwritable (mode: fmode) :=
  match mode with
  | RDONLY => false
  | WRONLY => true
  | RDWR => true
  end.

(* model of a simple "flat" filesystem *)

Inductive file: Type := mkfile: forall (size: nat) (contents: forall (ofs: nat), memval), file.

Definition fptr := nat.

(*typedef struct {
  int cur_dir; // i-node of the current working directory
  int n_inodes; // allocated i-nodes
  int n_open_files;
  uint8_t map_open_files[BITMAP_SIZE(N_INODES)];
  uint8_t map_inodes[BITMAP_SIZE(N_INODES)];
  uint8_t map_blocks[BITMAP_SIZE(N_BLOCKS)];
  uint32_t fd_map[MAX_OPEN_FILES]; // maps FDs to i-nodes
  uint32_t fptr_map[MAX_OPEN_FILES]; // maps FDs to file pointers
  file_mode_t fperm_map[MAX_OPEN_FILES]; // maps FDs to file permissions
  uint8_t block_cache[CACHE_N_BLOCKS][BLOCK_SIZE]; // data block cache
  uint32_t cache_map[CACHE_N_BLOCKS]; // maps cache block # to data block #
  // maps cache block # to approximate time since last access
  uint32_t cache_last_access_map[CACHE_N_BLOCKS];
} fs_data;*)

Inductive fs_data: Type := mkfsdata: forall
  (fdtable: forall (fd: int), option (fmode*fptr)) (*None = fd unused*)
  (fcache: forall (fd: int), option file) (*models in-memory storage*)
  (fnames: forall (fd: int), option int) (*map from file descriptors to file names*),
  fs_data.

Inductive fs: Type := mkfs: forall
  (MAX_FILE_DESCRIPTORS: int)
  (fsdata: fs_data)
  (fstore: forall (name: int), option file), (*models on-disk storage*)
  fs.

Section selectors.
Variable (fs: fs).
Definition get_max_fds := match fs with mkfs maxfds _ _ => maxfds end.
Definition get_fsdata := match fs with mkfs _ fsdata _ => fsdata end.
Definition get_fstore := match fs with mkfs _ _ fstore => fstore end.

Definition get_fdtable := match get_fsdata with mkfsdata fdtable _ _ => fdtable end.
Definition get_fcache := match get_fsdata with mkfsdata _ fcache _ => fcache end.
Definition get_fnames := match get_fsdata with mkfsdata _ _ fnames => fnames end.

Variable (fd: int).
Definition get_file := get_fcache fd.
Definition get_fmode :=
  match get_fdtable fd with
  | None => None
  | Some (md, cur) => Some md
  end.
Definition get_fptr :=
  match get_fdtable fd with
  | None => None
  | Some (md, cur) => Some cur
  end.

Variable (f: file).
Definition get_size := match f with mkfile sz _ => sz end.
Definition get_contents := match f with mkfile _ contents => contents end.

Definition isSome {A: Type} (a: option A) :=
  match a with
  | None => false
  | Some _ => true
  end.

Fixpoint get_nfiles_open_aux (n: nat) (fcache: int -> option (fmode*fptr)) :=
  match n with
  | O => O
  | S n' => if isSome (fcache (Int.repr (Z_of_nat n)))
              then S (get_nfiles_open_aux n' fcache)
              else get_nfiles_open_aux n' fcache
  end.

Definition get_nfiles_open :=
  get_nfiles_open_aux (nat_of_Z (Int.unsigned get_max_fds)) get_fdtable.

End selectors.

(*return the highest unallocated file descriptor, or None if none available*)
Section alloc_fd.
Variable (fs: fs).

Fixpoint find_unused_fd (n: nat) (fdtable: int -> option (fmode*fptr)) :=
  match n with
  | O => None
  | S n' => match fdtable (Int.repr (Z_of_nat n)) with
            | None => Some (Int.repr (Z_of_nat n))
            | Some _ => find_unused_fd n' fdtable
            end
  end.

Definition max_fds: nat := nat_of_Z (Int.unsigned (get_max_fds fs)).

Definition alloc_fd := find_unused_fd max_fds (get_fdtable fs).

Lemma alloc_fd_success :
  (get_nfiles_open fs < max_fds)%nat -> exists unused_fd, alloc_fd = Some unused_fd.
Proof.
unfold alloc_fd, find_unused_fd, max_fds.
unfold get_nfiles_open, get_max_fds.
destruct fs; hnf.
unfold get_fdtable.
simpl.
destruct fsdata; simpl.
forget (nat_of_Z (Int.unsigned MAX_FILE_DESCRIPTORS)) as n.
induction n.
inversion 1.
intros H1.
case_eq (fdtable (Int.repr (Z_of_nat (S n)))).
2: eexists; eauto.
intros [fm fp] H2.
simpl in H1.
simpl in H2.
rewrite H2 in H1.
simpl in H1.
eapply IHn.
apply lt_S_n; auto.
Qed.

End alloc_fd.

Definition MAX_FDS := Int.repr (Z_of_nat 1024).

Definition mount_fs (fstore: forall (name: int), option file) :=
  mkfs MAX_FDS (mkfsdata (fun _:int => None) (fun _:int => None) (fun _:int => None)) fstore.

Section FSExtension.
Variables
  (Z cT genv: Type)
  (csem: CoopCoreSem genv cT)
  (init_world: Z).

Local Open Scope nat_scope.

Inductive xT: Type := mkxT: forall (z: Z) (c: cT) (fs: fs), xT.

Section selectors.
Variable (s: xT).

Definition get_ext := match s with mkxT z _ _ => z end.
Definition get_core := match s with mkxT _ c _ => c end.
Definition get_fs := match s with mkxT _ _ fs => fs end.

End selectors.

Definition proj_core (i: nat) (s: xT) := if eq_nat_dec i 0 then Some (get_core s) else None.
Definition active := fun _: xT => 0.
Definition runnable := fun (s: xT) =>
  match at_external csem (get_core s), halted csem (get_core s) with
  | None, None => true
  | _, _ => false
  end.
Definition proj_zint (s: xT) := get_fs s.
Definition proj_zext (z: fs*Z) := snd z.
Definition zmult := @pair fs Z.

(*SYS_READ/WRITE_SIG: fd, buf, count*)
Notation SYS_READ_SIG := (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation SYS_WRITE_SIG := (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint)).
(*SYS_OPEN_SIG: name*)
Notation SYS_OPEN_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).

Notation SYS_READ := (EF_external 3%positive SYS_READ_SIG).
Notation SYS_WRITE :=  (EF_external 4%positive SYS_WRITE_SIG).
Notation SYS_OPEN := (EF_external 8%positive SYS_OPEN_SIG).

Definition int2fmode (i: int): option fmode :=
  if Int.eq i Int.zero then Some RDONLY
  else if Int.eq i Int.one then Some WRONLY
       else if Int.eq i (Int.repr 3%Z) then Some RDWR
            else None.
Definition val2oint (v: val): option int :=
  match v with
  | Vundef => None
  | Vint i => Some i
  | Vfloat _ => None
  | Vptr _ _ => None
  | Vlong _ => None (*LENB: is this ok, Gordon?*)
  end.

Definition address := (block * int)%type.
Definition val2oadr (v: val): option address :=
  match v with
  | Vundef => None
  | Vint i => None
  | Vlong i => None
  | Vfloat _ => None
  | Vptr b ofs => Some (b, ofs)
  end.

Definition val2omode (mode: val): option fmode :=
  match val2oint mode with Some i => int2fmode i | None => None end.

Section read_write.
Variable (f: file) (fptr: nat).

Let contents := get_contents f.

Fixpoint read_file_aux (nbytes sz cur: nat): list memval :=
  match nbytes with
  | O => nil
  | S nbytes' => if eq_nat_dec sz cur then nil
                 else contents cur :: read_file_aux nbytes' sz (S cur)
  end.

Lemma read_file_aux_length nbytes sz cur: length (read_file_aux nbytes sz cur) <= nbytes.
Proof.
revert cur; induction nbytes; auto.
simpl; intros cur.
if_tac.
simpl; omega.
simpl.
specialize (IHnbytes (S cur)).
apply le_n_S; auto.
Qed.

Lemma read_file_aux_end nbytes sz: read_file_aux nbytes sz sz = nil.
Proof.
induction nbytes; auto.
simpl.
if_tac; auto.
exfalso; auto.
Qed.

Lemma read_file_aux_id nbytes sz cur:
  read_file_aux nbytes sz cur =
  read_file_aux (length (read_file_aux nbytes sz cur)) sz cur.
Proof.
revert cur; induction nbytes; auto.
simpl; intros cur.
if_tac.
specialize (IHnbytes sz).
rewrite read_file_aux_end in IHnbytes; auto.
simpl.
if_tac; auto.
exfalso; auto.
simpl.
rewrite <-IHnbytes; auto.
Qed.

Lemma read_file_aux_length2 nbytes sz cur:
  length (read_file_aux nbytes sz cur) =
  length (read_file_aux (length (read_file_aux nbytes sz cur)) sz cur).
Proof.
revert cur; induction nbytes; auto.
simpl; intros cur.
if_tac.
specialize (IHnbytes sz).
rewrite read_file_aux_end in IHnbytes; auto.
simpl.
if_tac; auto.
exfalso; auto.
simpl.
rewrite <-IHnbytes; auto.
Qed.

Lemma loadbytes_read_file_le m b ofs nbytes0 nbytes sz cur:
  nbytes0 <= nbytes ->
  Mem.loadbytes m b ofs (Z_of_nat nbytes) = Some (read_file_aux nbytes sz cur) ->
  Mem.loadbytes m b ofs (Z_of_nat nbytes0) = Some (read_file_aux nbytes0 sz cur).
Proof.
revert ofs cur nbytes0; induction nbytes; simpl; auto.
destruct nbytes0; try omega; auto.
try (intros; omegaContradiction). (* Coq 8.3/8.4 compat *)
intros ofs cur nbytes0 H1.
destruct nbytes0.
simpl; intros; apply Mem.loadbytes_empty; omega.
if_tac.
rewrite H in *.
Transparent Mem.loadbytes.
unfold Mem.loadbytes.
intros H2.
if_tac in H2; try congruence.
inv H2.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H4.
simpl in H4.
inv H4.
simpl.
if_tac.
elimtype False; auto.
intros H2.
unfold Mem.loadbytes in H2.
if_tac in H2; try congruence.
simpl in H2.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H2.
simpl in H2.
inversion H2; subst.
specialize (IHnbytes (ofs+1)%Z (S cur) nbytes0).
spec IHnbytes.
omega.
assert (H7: Mem.range_perm m b (ofs+1) (ofs+1 + Z_of_nat nbytes) Cur Readable).
 unfold Mem.range_perm in H3|-*.
 intros ofs'; specialize (H3 ofs').
 intros [H4 H7]; spec H3.
 split. omega. rewrite Zpos_P_of_succ_nat. omega.
 auto.
spec IHnbytes.
unfold Mem.loadbytes.
if_tac; try congruence.
f_equal.
rewrite nat_of_Z_of_nat.
rewrite H6; auto.
rewrite Zpos_P_of_succ_nat.
unfold Mem.loadbytes in IHnbytes|-*.
assert (H8: Mem.range_perm m b ofs (ofs + Zsucc (Z_of_nat nbytes0)) Cur Readable).
 unfold Mem.range_perm in H3|-*.
 intros ofs'; specialize (H3 ofs').
 intros [H4 H9]; spec H3.
 split. omega. rewrite Zpos_P_of_succ_nat. omega.
 auto.
if_tac in IHnbytes.
inversion IHnbytes; subst.
if_tac; try congruence.
rewrite <-inj_S.
do 2 rewrite nat_of_Z_of_nat.
simpl.
f_equal.
f_equal; auto.
congruence.
Qed.

Definition read_file (nbytes: nat): list memval := read_file_aux nbytes (get_size f) fptr.

Fixpoint write_file_aux (bytes: list memval) (sz cur: nat): (nat -> memval)*nat :=
  match bytes with
  | nil => (contents, O)
  | byte::bytes' =>
    match write_file_aux bytes' sz (S cur) with (contents', nbytes) =>
        (fun ofs => if eq_nat_dec ofs cur then byte else contents' ofs, S nbytes)
    end
  end.

Lemma write_file_aux_length (bytes: list memval) (sz cur: nat):
  snd (write_file_aux bytes sz cur)=length bytes.
Proof.
revert cur; induction bytes; auto.
intros cur; simpl.
specialize (IHbytes (S cur)).
destruct (write_file_aux bytes sz (S cur)).
simpl.
f_equal.
auto.
Qed.

Definition write_file (bytes: list memval): file*nat :=
  match write_file_aux bytes (get_size f) fptr with (contents, nwritten) =>
    (mkfile (get_size f + (fptr + nwritten - get_size f)) (get_contents f), nwritten)
  end.

End read_write.

Section fs_read_write.
Variables (fsys: fs) (fd: int).

Definition fs_read (nbytes: nat): option (list memval) :=
  match get_file fsys fd, get_fptr fsys fd with
  | Some f, Some cur => Some (read_file f cur nbytes)
  | _, _ => None
  end.

Definition fs_write (bytes: list memval): option (nat(*nbytes written*)*fs) :=
  match get_file fsys fd, get_fptr fsys fd, get_fmode fsys fd with
  | Some file, Some cur, Some md =>
    if fwritable md then
      match write_file file cur bytes with (new_file, nbytes_written) =>
        Some (nbytes_written,
              mkfs (get_max_fds fsys)
                   (mkfsdata (fun i => if Int.eq fd i then Some (md, cur + nbytes_written)
                                       else get_fdtable fsys i)
                             (fun i => if Int.eq fd i then Some new_file
                                       else get_fcache fsys i)
                             (get_fnames fsys))
                   (get_fstore fsys))
       end
     else None
  | _, _, _ => None
  end.

Lemma fs_write_length bytes n fs: fs_write bytes = Some (n, fs) -> n=length bytes.
Proof.
unfold fs_write.
destruct (get_file fsys fd); try congruence.
destruct (get_fptr fsys fd); try congruence.
destruct (get_fmode fsys fd); try congruence.
if_tac; try congruence.
case_eq (write_file f f0 bytes); try congruence.
intros f2 n0 H1 H2.
inv H2.
unfold write_file in H1.
case_eq (write_file_aux f bytes (get_size f) f0); try congruence.
intros m n0 H2.
rewrite H2 in H1.
inv H1.
rewrite <-write_file_aux_length
 with (f := f) (sz := get_size f) (cur := f0), H2.
auto.
Qed.

End fs_read_write.

Definition new_file := mkfile O (fun _:nat => Undef).

Section fs_open.
Variable (fsys: fs) (unused_fd: int).

Definition fs_open_existing (fname: int) (f: file) (md: fmode): fs :=
  mkfs (get_max_fds fsys)
       (mkfsdata (fun i => if Int.eq i unused_fd then Some (md, O)
                           else get_fdtable fsys i)
                 (fun i => if Int.eq i unused_fd then Some f
                           else get_fcache fsys i)
                 (fun i => if Int.eq i unused_fd then Some fname
                           else get_fnames fsys i))
       (get_fstore fsys).

Definition fs_open_new (fname: int) (md: fmode): fs :=
  mkfs (get_max_fds fsys)
       (mkfsdata (fun i => if Int.eq i unused_fd then Some (md, O)
                           else get_fdtable fsys i)
                 (fun i => if Int.eq i unused_fd then Some new_file
                           else get_fcache fsys i)
                 (fun i => if Int.eq i unused_fd then Some fname
                           else get_fnames fsys i))
       (get_fstore fsys).

Definition fs_open (fname: int) (md: fmode): option fs :=
  match fwritable md, get_fstore fsys fname with
  | false, Some f => Some (fs_open_existing fname f md)
  | false, None => None
  | true, Some f => Some (fs_open_existing fname f md)
  | true, None => Some (fs_open_new fname md)
  end.

End fs_open.

Definition handled_list: list AST.external_function := SYS_READ::SYS_WRITE::SYS_OPEN::nil.

Definition is_open (fsys: fs) (fname: int) := exists fd, get_fnames fsys fd = Some fname.

Definition is_readable (fsys: fs) (fd: int) :=
  exists md, exists cur, exists f,
    get_fdtable fsys fd = Some (md, cur) /\ get_fcache fsys fd = Some f.

Definition is_writable (fsys: fs) (fd: int) :=
  exists md, exists cur, exists f,
    get_fdtable fsys fd = Some (md, cur) /\ fwritable md=true /\
    get_fcache fsys fd = Some f.

Inductive os_step: genv -> xT -> mem -> xT -> mem -> Prop :=
| os_corestep: forall ge z c fs m c' m',
  corestep csem ge c m c' m' ->
  os_step ge (mkxT z c fs) m (mkxT z c' fs) m'
| os_open: forall ge z s m c md0 fname0 md fname unused_fd fs',
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_OPEN, SYS_OPEN_SIG, fname0::md0::nil) ->
  alloc_fd fs = Some unused_fd ->
  val2omode md0 = Some md ->
  val2oint fname0 = Some fname ->
  ~is_open fs fname ->
  fs_open fs unused_fd fname md = Some fs' ->
  after_external csem (Some (Vint unused_fd)) (get_core s) = Some c ->
  os_step ge s m (mkxT z c fs') m
| os_read: forall ge z s m c fd0 fd buf adr nbytes0 nbytes bytes m',
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_READ, SYS_READ_SIG, fd0::buf::nbytes0::nil) ->
  val2oint fd0 = Some fd ->
  val2oadr buf = Some adr ->
  val2oint nbytes0 = Some nbytes ->
  fs_read fs fd (nat_of_Z (Int.unsigned nbytes)) = Some bytes ->
  Forall is_defchar bytes ->
  (Zlength bytes > 0)%Z ->
  Mem.storebytes m (fst adr) (Int.unsigned (snd adr)) bytes = Some m' ->
  after_external csem (Some (Vint (Int.repr (Zlength bytes)))) (get_core s) = Some c ->
  os_step ge s m (mkxT z c fs) m'
(*| os_write: forall ge z s m c fd0 fd adr buf nbytes0 nbytes bytes fs' nbytes_written sig,
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_WRITE, sig, fd0::buf::nbytes0::nil) ->
  val2oint fd0 = Some fd ->
  val2oadr buf = Some adr ->
  val2oint nbytes0 = Some nbytes ->
  Mem.loadbytes m (fst adr) (Int.unsigned (snd adr)) (Int.unsigned nbytes) = Some bytes ->
  fs_write fs fd bytes = Some (nbytes_written, fs') ->
  after_external csem (Some (Vint (Int.repr (Z_of_nat nbytes_written)))) (get_core s) = Some c ->
  os_step ge s m (mkxT z c fs') m*).

Definition os_initial_core (ge: genv) (v: val) (args: list val): option xT :=
  match initial_core csem ge v args with
  | Some c => Some (mkxT init_world c (mount_fs (fun _: int => None)))
  | None => None
  end.

Definition os_at_external (s: xT) :=
  match at_external csem (get_core s) with
  | Some (SYS_READ, sig, args) => None
  | Some (SYS_WRITE, sig, args) => None
  | Some (SYS_OPEN, sig, args) => None
  | Some (ef, sig, args) => Some (ef, sig, args)
  | None => None
  end.

 Lemma os_at_external_core1: forall s ef sig args,
  os_at_external s = Some (ef, sig, args) ->
  at_external csem (get_core s) = Some (ef, sig, args).
 Proof.
 intros until args; intros H1.
 unfold os_at_external in H1.
 destruct (at_external csem (get_core s)); try solve[inv H1].
 destruct p.
 destruct p.
 destruct e; auto.
 destruct name; auto.
 destruct name; auto.
 destruct sg; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct sig_res; auto.
 destruct t; auto.
 congruence.
 destruct name; auto.
 destruct name; auto.
 destruct name; auto.
 destruct sg; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct sig_res; auto.
 destruct t; auto.
 congruence.
 destruct sg; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct sig_res; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t0; auto.
 congruence.
 destruct t; auto.
 destruct sig_args; auto.
 Qed.

 Lemma os_at_external_core2: forall s ef sig args,
  at_external csem (get_core s) = Some (ef, sig, args) ->
  ef<>SYS_READ ->
  ef<>SYS_WRITE ->
  ef<>SYS_OPEN ->
  os_at_external s = Some (ef, sig, args).
 Proof.
 intros until args; intros H1.
 destruct s.
 unfold os_at_external.
 simpl in *.
 rewrite H1.
 destruct ef; auto.
 destruct name; auto.
 destruct name; auto.
 destruct sg; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct sig_res; auto.
 destruct t; auto.
 congruence.
 destruct name; auto.
 destruct name; auto.
 destruct name; auto.
 destruct sg; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct sig_res; auto.
 destruct t; auto.
 congruence.
 destruct sg; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct sig_res; auto.
 destruct t; auto.
 destruct sig_args; auto.
 destruct t0; auto.
 congruence.
 destruct t; auto.
 destruct sig_args; auto.
 Qed.

 Lemma os_at_external_core3: forall s ef sig args,
  at_external csem (get_core s) = Some (ef, sig, args) ->
  ef=SYS_READ \/ ef=SYS_WRITE \/ ef=SYS_OPEN ->
  os_at_external s = None.
 Proof.
 intros until args; intros H1.
 destruct s.
 unfold os_at_external.
 intros H.
 destruct H; subst.
 rewrite H1; auto.
 rewrite H1; auto.
 destruct H; subst; auto.
 Qed.

 Lemma os_at_external_core4: forall s ef sig args,
  at_external csem (get_core s) = Some (ef, sig, args) ->
  os_at_external s = None ->
  ef=SYS_READ \/ ef=SYS_WRITE \/ ef=SYS_OPEN.
 Proof.
 intros until args; intros H1.
 destruct s.
 intros H.
 unfold os_at_external in H.
 rewrite H1 in H.
 destruct ef; try congruence.
 destruct name; try congruence.
 destruct name; try congruence.
 destruct sg; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct sig_res; try congruence.
 destruct t; try congruence.
 left; auto.
 destruct name; try congruence.
 destruct name; try congruence.
 destruct name; try congruence.
 destruct sg; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct sig_res; try congruence.
 destruct t; try congruence.
 right. right; auto.
 destruct sg; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct t; try congruence.
 destruct sig_args; try congruence.
 destruct sig_res; try congruence.
 destruct t; try congruence.
 right. left; auto.
 Qed.

Definition os_after_external (ov: option val) (s: xT): option xT :=
  match after_external csem ov (get_core s) with
  | Some c => Some (mkxT (get_ext s) c (get_fs s))
  | None => None
  end.

Definition os_halted (s: xT): option val :=
  halted csem (get_core s).

Program Definition FSCoreSem := Build_CoreSemantics genv xT mem
  os_initial_core
  os_at_external
  os_after_external
  os_halted
  os_step
  _ _ _ _.
Next Obligation.
case_eq (at_external csem (get_core q)).
2: unfold os_at_external; intros H1; rewrite H1; auto.
intros [[ef sig] args] H1.
inv H.
apply corestep_not_at_external in H0; simpl in H1; congruence.
unfold os_at_external; rewrite H0; auto.
unfold os_at_external; rewrite H0; auto.
(*unfold os_at_external; rewrite H0; auto.*)
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H0; simpl; auto.
edestruct (at_external_halted_excl csem); eauto. congruence.
edestruct (at_external_halted_excl csem); eauto. congruence.
(*edestruct (at_external_halted_excl csem); eauto. congruence.*)
Qed.
Next Obligation.
edestruct (at_external_halted_excl csem); eauto.
left; unfold os_at_external; rewrite H; auto.
Qed.
Next Obligation.
unfold os_after_external in H|-*.
case_eq (after_external csem retv (get_core q)).
intros c H1.
rewrite H1 in H.
inv H.
apply after_at_external_excl in H1.
unfold os_at_external.
simpl; rewrite H1; auto.
intros H1; rewrite H1 in H; congruence.
Qed.

Program Definition FSCoopSem :=
  Build_CoopCoreSem _ _ FSCoreSem _.
Next Obligation.
inv CS.
destruct csem.
destruct coopsem.
eapply corestep_fwd; eauto.
solve[apply mem_lemmas.mem_forward_refl].
solve[eapply mem_lemmas.storebytes_forward; eauto].
Qed.
(*
Next Obligation.
inv CS.
destruct csem.
eapply corestep_wdmem; eauto.
auto.
eapply mem_lemmas.mem_wd_storebytes; eauto.
intros v IN.
clear - H5 IN.
induction bytes.
simpl in IN; inv IN.
simpl in IN.
destruct IN. subst. inv H5.
destruct v; simpl in H1; try inv H1.
solve[apply memval_inject_byte].
apply IHbytes; auto.
solve[inv H5; auto].
Qed.
*)

Definition file_exists (fsys: fs) (fname: int) := isSome (get_fstore fsys fname).

Definition fs_pre (ef: AST.external_function) u (typs: list typ) args (fsz: fs*Z) m :=
  match ef, fsz, args with
  | SYS_OPEN, (fsys, z), fname0::md0::nil =>
    match val2oint fname0, val2omode md0 with
    | Some fname, Some md =>
        List.Forall2 Val.has_type (md0::nil) (sig_args SYS_OPEN_SIG) /\
        get_nfiles_open fsys < nat_of_Z (Int.unsigned (get_max_fds fsys)) /\
        (~file_exists fsys fname=true -> fwritable md=true) /\
        ~is_open fsys fname
    | _, _ => False
    end
  | SYS_READ, (fsys, z), (fd0::buf::nbytes0::nil) =>
    match val2oint fd0, val2oadr buf, val2oint nbytes0 with
    | Some fd, Some adr, Some nbytes =>
        u=adr /\
        List.Forall2 Val.has_type (fd0::buf::nbytes0::nil) (sig_args SYS_READ_SIG) /\
        is_readable fsys fd /\
        Mem.range_perm m (fst adr) (Int.unsigned (snd adr))
                         (Int.unsigned (snd adr) + Int.unsigned nbytes) Cur Writable
    | _, _, _ => False
    end
  | SYS_WRITE, (fsys, z), (fd0::buf::nbytes0::nil) =>
    match val2oint fd0, val2oadr buf, val2oint nbytes0 with
    | Some fd, Some adr, Some nbytes =>
        u=adr /\
        List.Forall2 Val.has_type (fd0::buf::nbytes0::nil) (sig_args SYS_WRITE_SIG) /\
        is_writable fsys fd /\
        Mem.range_perm m (fst adr) (Int.unsigned (snd adr))
                         (Int.unsigned (snd adr) + Int.unsigned nbytes) Cur Readable
     | _, _, _ => False
     end
  | _, _, _ => False
  end.

Definition obind {A B: Type} (d: B) (o: option A) (f: A -> B) :=
  match o with Some a => f a | None => d end.

(*TODO: to make fs_post more precise, we'll have to add more information
   to the shared parameter x, i.e., the fd and fptr for file read/written*)
Definition fs_post (ef: AST.external_function) (adr: address) (ty: option typ)
                   retval0 (fsz: fs*Z) (m: mem) :=
  match ef, fsz with
  | SYS_OPEN, (fsys, z) => obind False retval0 (fun retval =>
      obind False (val2oint retval) (fun fd => is_readable fsys fd))
  | SYS_READ, (fsys, z) => obind False retval0 (fun retval =>
      obind False (val2oint retval) (fun nbytes =>
        exists bytes,
          nbytes=Int.repr (Zlength bytes) /\
          Mem.loadbytes m (fst adr) (Int.unsigned (snd adr)) (Int.unsigned nbytes) = Some bytes))
  | SYS_WRITE, (fsys, z) => True
  | _, _ => True
  end.

Definition Client_FSExtSpec :=
  Build_external_specification Memory.mem AST.external_function (fs*Z)
  (fun ef: AST.external_function => address) fs_pre fs_post.

Lemma fs_ext_pf3:
  forall (s : xT) (c : cT) (s' : xT) (c' : cT) (ef : external_function)
  (sig : signature) (args : list val) (sig' : signature)
  (args' : list val),
  get_core s = c ->
  at_external csem c = Some (ef, sig, args) ->
  at_external FSCoreSem s = None ->
  get_core s' = c' ->
  at_external csem c' = Some (ef, sig', args') ->
  at_external FSCoreSem s' = None.
Proof.
intros.
exploit os_at_external_core4; eauto.
rewrite H.
eauto.
intros.
eapply os_at_external_core3; eauto.
rewrite H2; eauto.
Qed.

Program Definition FS_extension: Extension.Sig (Z*fs) fs Z FSCoreSem _ _ csem :=
  @Extension.Make _ _ _ _ _ _ FSCoreSem _ _ csem
    get_core get_fs fst (fun (x: fs) (y: Z) => (y, x))
    _ _ _ fs_ext_pf3.
Next Obligation.
unfold os_after_external in H0.
case_eq (after_external csem ret (get_core s)).
intros.
rewrite H1 in H0.
inv H0.
simpl; auto.
intros.
rewrite H1 in H0.
congruence.
Qed.
Next Obligation.
apply corestep_not_at_external in H.
inv H0; simpl; auto; rewrite H in H1; congruence.
Qed.

Variable csem_det:
  forall ge c m c' m' c'' m'',
  corestep csem ge c m c' m' ->
  corestep csem ge c m c'' m'' ->
  c'=c'' /\ m'=m''.

Lemma FS_core_compat:
  forall ge, @core_compatible _ _ _ _ _ _  FSCoreSem  _ _ _ ge ge FS_extension.
Proof.
intros.
constructor; auto.
(*goal 1*)
intros.
simpl.
simpl in H0.
unfold c in *.
inv H0.
simpl in H. simpl. auto.
simpl in *. unfold linking.runnable in H. rewrite H1 in H. congruence.
simpl in *. unfold linking.runnable in H. rewrite H1 in H. congruence.
(*simpl in *. unfold linking.runnable in H. rewrite H1 in H. congruence.*)
(*goal 2*)
intros.
simpl in H0.
unfold c in *.
inv H0.
simpl.
simpl in H.
eapply csem_det in H1; eauto.
solve[destruct H1; auto].
simpl in *.
apply corestep_not_at_external in H.
rewrite H in H1.
congruence.
apply corestep_not_at_external in H.
simpl in H.
rewrite H in H1.
congruence.
(*apply corestep_not_at_external in H.
simpl in H.
rewrite H in H1.
congruence.*)
(*goal 3*)
intros.
destruct s.
exists (mkxT z c' fs0).
unfold c in *.
simpl in H.
split.
solve[apply os_corestep; auto].
solve[auto].
(*goal 4*)
intros.
solve[exploit os_at_external_core1; eauto].
(*goal 5*)
intros.
unfold c in *.
simpl in H.
destruct s.
exists (mkxT z c' fs0).
simpl.
split; auto.
unfold os_after_external.
rewrite H.
auto.
Qed.

End FSExtension.

Section FSExtension_Compilable.
Variables
(Z S T fS vS fT vT: Type)
(init_world: Z)
(csemS: CoopCoreSem (Genv.t fS vS) S)
(csemT: CoopCoreSem (Genv.t fT vT) T)
(geS: Genv.t fS vS)
(geT: Genv.t fT vT)
(entry_points: list (val*val*signature))
(core_data: Type)
(core_ord: core_data -> core_data -> Prop)
(MATCH: core_data -> meminj -> S -> mem -> T -> mem -> Prop).

Definition FS_S := FS_extension csemS init_world.
Definition FS_T := FS_extension csemT init_world.

Import Forward_simulation_inj_exposed.

Variable coreSim:
  Forward_simulation_inject csemS csemT geS geT entry_points
    core_data MATCH core_ord.

Variable genvs_eq: genvs_domain_eq geS geT.


(*ASSUMPTIONS*)
Variable csemS_det:
  forall (ge : Genv.t fS vS) (c : S) (m : mem) (c' : S)
  (m' : mem) (c'' : S) (m'' : mem),
  corestep csemS ge c m c' m' ->
  corestep csemS ge c m c'' m'' -> c' = c'' /\ m' = m''.
Variable csemT_det:
  forall (ge : Genv.t fT vT) (c : T) (m : mem) (c' : T)
  (m' : mem) (c'' : T) (m'' : mem),
  corestep csemT ge c m c' m' ->
  corestep csemT ge c m c'' m'' -> c' = c'' /\ m' = m''.
Variable match_state_runnable:
   forall (cd : core_data) (j : meminj) (c1 : S) (m1 : mem)
     (c2 : T) (m2 : mem),
   MATCH cd j c1 m1 c2 m2 ->
   linking.runnable csemS c1 = linking.runnable csemT c2.
Variable match_state_meminj:
   forall (cd : core_data) (j : meminj) (c1 : S) (m1 : mem)
   (c2 : T) (m2 : mem), MATCH cd j c1 m1 c2 m2 -> Mem.inject j m1 m2.
Variable match_preserves_globs:
   forall (cd : core_data) (j : meminj) (c1 : S) (m1 : mem)
     (c2 : T) (m2 : mem),
   MATCH cd j c1 m1 c2 m2 -> meminj_preserves_globals geS j.
Variable at_extern_valid:
  forall c1 m1 c2 m2 cd j ef sig args,
    MATCH cd j c1 m1 c2 m2 ->
    at_external csemS c1 = Some (ef, sig, args) ->
    forall v, In v args -> mem_lemmas.val_valid v m1.


Lemma FS_extension_compilable:
  @CompilableExtension.Sig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (FSCoopSem csemS init_world)
  (FSCoopSem csemT init_world)
  csemS csemT
  geS geT FS_S FS_T entry_points core_data MATCH core_ord.
Proof.
destruct (@ExtensionCompilability.ExtensionCompilability
   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (FSCoopSem csemS init_world)
  (FSCoopSem csemT init_world)
  csemS csemT
  geS geT geS geT FS_S FS_T entry_points core_data MATCH core_ord) as [L].
intros.
eapply at_extern_valid; eauto.
apply L; auto.
apply genvs_domain_eq_refl.
apply genvs_domain_eq_refl.
apply FS_core_compat.
apply csemS_det.
apply FS_core_compat.
apply csemT_det.
constructor; auto.

(*1: handled steps*)
intros until j.
simpl in *.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 STEP.
inv STEP.

(*fs_open*)
apply corestep_not_at_external in H.
simpl in H3. rewrite H in H3. congruence.
destruct s1; simpl in *.
destruct s2; simpl in *.

assert (exists cd' c0' c1',
        after_external csemS (Some (Vint unused_fd)) c0 = Some c0' /\
        after_external csemT (Some (Vint unused_fd)) c1 = Some c1' /\
        MATCH cd' j c0' m1' c1' m2).
 destruct coreSim.
 clear core_diagram0 core_initial0 core_at_external0 core_halted0.
 specialize (core_after_external0
  cd j j c0 c1 m1'
  (EF_external 8%positive {| sig_args := Tint :: Tint :: nil; sig_res := Some Tint |})
  args1 (Vint unused_fd)
  m1' m2 m2
  (Vint unused_fd)
  sig).
spec core_after_external0; auto.
spec core_after_external0; auto.
unfold CompilabilityInvariant.match_states in H5.
destruct H5; auto.
spec core_after_external0; auto.
rewrite H.
rewrite H in H3.
inv H3.
solve[auto].
spec core_after_external0; auto.
intros.
destruct H5 as [M1 M2].
rewrite H3 in H.
inv H.
solve[eapply at_extern_valid; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[apply mem_lemmas.inject_separated_same_meminj].
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[apply mem_lemmas.mem_forward_refl].
spec core_after_external0; auto.
solve[apply Mem.unchanged_on_refl].
spec core_after_external0; auto.
solve[apply mem_lemmas.mem_forward_refl].
spec core_after_external0; auto.
solve[apply Mem.unchanged_on_refl].
spec core_after_external0; auto.
rewrite H3 in H.
inv H.
solve[simpl; auto].
destruct H5 as [H5 XX].
(*exploit match_memwd0; eauto.
intros [? ?].*)
(*spec core_after_external0; auto.
spec core_after_external0; auto.*)
spec core_after_external0; simpl; auto.
solve[spec core_after_external0; simpl; auto].

destruct H15 as [cd' [c0' [c1' [AFT1 [AFT2 MM]]]]].
exists (mkxT z c1' fs'), m2, cd', j.
split; auto.
split; auto.
solve[apply mem_lemmas.inject_separated_same_meminj].
split; auto.
unfold CompilabilityInvariant.match_states.
simpl.
assert (c = c0') as ->.
  rewrite AFT1 in H14.
  solve[inv H14; auto].
solve[auto].
split.
solve[apply Mem.unchanged_on_refl].
split.
solve[apply Mem.unchanged_on_refl].
left.
exists O.
simpl.
exists (mkxT z c1' fs'), m2.
split; auto.
destruct H5 as [H5 XX].
simpl in XX.
subst fs2.
apply os_open
 with (md0 := md0) (fname0 := fname0)
      (md := md) (fname := fname) (unused_fd := unused_fd); auto.
simpl.
rewrite H4.
rewrite H in H3.
inv H3.
assert (args2 = fname0 :: md0 :: nil) as ->.
 destruct args2.
 inversion H8.
 destruct args2.
 inversion H8; subst.
 inv H19.
 inversion H8; subst.
 destruct args2.
 inversion H19; subst.
 f_equal; auto.
 unfold val2oint in H11.
 inv H17; auto; try congruence.
 unfold val2omode in H10.
 inv H18; auto; try congruence.
 simpl in H10; congruence.
 simpl in H10; congruence.
 inv H19.
 solve[inv H21].
auto.

(*fs_read*)
destruct s1, s2; simpl in *.

assert (exists m2' b' ofs',
        Mem.storebytes m2 b' (Int.unsigned ofs') bytes = Some m2' /\
        Mem.inject j m1' m2' /\
        Mem.unchanged_on (loc_unmapped j) m1 m1' /\
        Mem.unchanged_on (loc_out_of_reach j m1) m2 m2' /\
        (exists delta, j (fst adr) = Some (b',delta) /\
          ofs' = Int.add (snd adr) (Int.repr delta))).
 destruct adr.
 simpl in H13|-*.
 rewrite H3 in H.
 inversion H.
 subst args1.
 assert (buf = Vptr b i).
  unfold val2oadr in H10.
  destruct buf; try congruence; try inv H10.
 subst buf.
 assert (exists b' delta, j b = Some (b', delta)).
  inversion H8.
  inversion H23.
  subst x0.
  inversion H26.
  subst y0.
  exists b2, delta.
  solve[auto].
 destruct H17 as [b' [delta JJ]].
 eapply storebytes_sem_inject_comm
  with (m2 := m2) (j := j) (b' := b') in H13; eauto.
 destruct H13 as [m2' [? [? [? ?]]]].
 exists m2', b', (Int.add i (Int.repr delta)).
 split; auto.
 split; auto.
 split; auto.
 split; auto.
 solve[exists delta; auto].
destruct H17 as [m2' [b' [ofs' [H17 [INJ [UNCH1 [UNCH2 XX]]]]]]].
assert (exists cd' c0' c1',
        after_external csemS (Some (Vint (Int.repr (Zlength bytes)))) c0 = Some c0' /\
        after_external csemT (Some (Vint (Int.repr (Zlength bytes)))) c1 = Some c1' /\
        MATCH cd' j c0' m1' c1' m2').
 destruct coreSim.
 clear core_diagram0 core_initial0 core_at_external0 core_halted0.
 specialize (core_after_external0
  cd j j c0 c1 m1
  (EF_external 3%positive
        {| sig_args := Tint :: Tint :: Tint :: nil; sig_res := Some Tint |})
  args1 (Vint (Int.repr (Zlength bytes)))
  m1' m2 m2'
  (Vint (Int.repr (Zlength bytes)))
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
spec core_after_external0; auto.
destruct H5. simpl in H5.
spec core_after_external0; auto.
spec core_after_external0; auto.
rewrite H.
rewrite H3 in H.
inv H.
solve[auto].
spec core_after_external0; auto.
rewrite H3 in H.
inv H.
solve[eapply at_extern_valid; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[apply mem_lemmas.inject_separated_same_meminj].
spec core_after_external0; auto.
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[eapply mem_lemmas.storebytes_forward; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[eapply mem_lemmas.storebytes_forward; eauto].
spec core_after_external0; auto.
spec core_after_external0; auto.
solve[simpl; auto].
(*spec core_after_external0; auto.

eapply mem_lemmas.mem_wd_storebytes; eauto.
edestruct (FSCoopSem csemS).
refine init_world.
exploit match_memwd0; eauto.
solve[intros [? ?]; auto].
intros v IN.
clear - H13 IN.
induction bytes.
simpl in IN; inv IN.
simpl in IN.
destruct IN. subst. inv H13.
destruct v; simpl in H1; try inv H1.
solve[apply memval_inject_byte].
apply IHbytes; auto.
solve[inv H13; auto].
spec core_after_external0; auto.
eapply mem_lemmas.mem_wd_storebytes; eauto.
edestruct (FSCoopSem csemT).
refine init_world.
exploit match_memwd0; eauto.
solve[intros [? ?]; auto].
intros v IN.
clear - H13 IN.
induction bytes.
simpl in IN; inv IN.
simpl in IN.
destruct IN. subst. inv H13.
destruct v; simpl in H1; try inv H1.
solve[apply memval_inject_byte].
apply IHbytes; auto.
solve[inv H13; auto].
*)
spec core_after_external0; auto.
solve[simpl; auto].
spec core_after_external0; auto.
solve[simpl; auto].
destruct H18 as [cd' [c0' [c1' [? [? ?]]]]].

exists (mkxT z c1' fs0), m2', cd', j.
split; auto.
split; auto.
apply mem_lemmas.inject_separated_same_meminj.
split; auto.
split; auto.
simpl.
rewrite H16 in H18; inv H18.
solve[auto].
split; auto.
split; auto.
left.
exists O.
simpl.
exists (mkxT z c1' fs0), m2'.
split; auto.
assert (fs0 = get_fs (mkxT z1 c1 fs2)) as ->.
  simpl.
  unfold fs0.
  destruct H5.
  solve[auto].
apply os_read
 with (fd0 := fd0)
      (fd := fd)
      (buf := Vptr b' ofs')
      (adr := (b',ofs'))
      (nbytes0 := nbytes0)
      (nbytes := nbytes)
      (bytes := bytes); auto.
simpl.
rewrite H4.
rewrite H in H3.
inv H3.
f_equal; auto.
f_equal; auto.

destruct XX as [delta [XX YY]].
destruct adr.
simpl in XX.
clear - XX YY H8 H0 H10 H11.
destruct args2; simpl in H8; try inv H8.
destruct args2; simpl in H5; try inv H5.
unfold val2oint,val2oadr in *.
destruct fd0; try congruence.
destruct buf; try congruence.
destruct nbytes0; try congruence.
inv H0; inv H10; inv H11.
inv H3.
inv H4.
inv H7.
simpl.
rewrite H1 in XX; inv XX.
inv H2.
inv H4.
solve[auto].

(*goal 2*)
intros.
simpl in *.
unfold os_at_external in *.
unfold c1 in *.
unfold c2 in *.
simpl in H1,H7.
rewrite H7.
rewrite H1 in H0.
destruct ef; auto.
destruct name; auto.
destruct name; auto.
destruct sg; auto.
destruct sig_args; auto.
destruct t; auto.
destruct sig_args; auto.
destruct t; auto.
destruct sig_args; auto.
destruct t; auto.
destruct sig_args; auto.
destruct sig_res; auto.
destruct t; auto.
congruence.
destruct name; auto.
destruct name; auto.
destruct sg; auto.
destruct sig_args; auto.
destruct name; auto.
destruct t; auto.
destruct sig_args; auto.
destruct name; auto.
destruct t; auto.
destruct sig_args; auto.
destruct name; auto.
destruct sig_res; auto.
destruct t; auto.
congruence.
destruct name; auto.
destruct name; auto.
destruct name; auto.
destruct name; auto.
destruct name; auto.
destruct name; auto.
destruct name; auto.
destruct sg; auto.
destruct sig_args; auto.
destruct t; auto.
destruct sig_args; auto.
destruct t; auto.
destruct sig_args; auto.
destruct t; auto.
destruct sig_args; auto.
destruct sig_res; auto.
destruct t; auto.
congruence.

(*goal 3*)
intros.
simpl in H0|-*.
unfold os_initial_core in H0|-*.
case_eq (initial_core csemS geS v1 vals1).
intros s INIT.
rewrite INIT in H0.
inv H0.
destruct coreSim.
clear
 core_diagram0
 core_halted0
 core_at_external0
 core_after_external0.
eapply core_initial0 in INIT; eauto.
destruct INIT as [cd [c2 [INIT MATCH']]].
rewrite INIT.
exists cd; eexists; split; eauto.
split. simpl. auto. simpl; auto.
intros NONE.
rewrite NONE in H0.
congruence.

(*goal 4*)
intros.
destruct coreSim.
clear
 core_diagram0
 core_initial0
 core_at_external0
 core_after_external0.
destruct H as [H2 H3].
solve[eapply core_halted0 in H2; eauto].
Qed.

End FSExtension_Compilable.
