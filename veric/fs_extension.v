Load loadpath.
Require Import msl.base. (*for spec tac*)

Require Import veric.sim.
Require Import veric.step_lemmas.
Require Import veric.extspec.
Require Import veric.extension.
Require Import veric.extension_sim.
Require Import veric.extension_proof.
Require Import veric.Address.
Require Import veric.juicy_mem.
Require Import veric.juicy_extspec.
Require Import veric.Coqlib2.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

Definition genv := Genv.t Clight.fundef Ctypes.type.

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
  (Z cT D: Type) 
  (csem: CoreSemantics genv cT mem D)
  (init_world: Z).

Definition cores := fun _:nat => csem.

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
  match at_external csem (get_core s), safely_halted csem (get_core s) with 
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
  end.

Definition val2oadr (v: val): option address :=
  match v with
  | Vundef => None
  | Vint i => None
  | Vfloat _ => None
  | Vptr b ofs => Some (b, Int.unsigned ofs)
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
spec IHnbytes sz.
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
spec IHnbytes sz.
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
intros; omegaContradiction.
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
spec IHnbytes (ofs+1)%Z (S cur) nbytes0.
spec IHnbytes.
omega.
assert (H7: Mem.range_perm m b (ofs+1) (ofs+1 + Z_of_nat nbytes) Cur Readable).
 unfold Mem.range_perm in H3|-*.
 intros ofs'; spec H3 ofs'.
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
 intros ofs'; spec H3 ofs'.
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
spec IHbytes (S cur).
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

Definition handled: list AST.external_function := SYS_READ::SYS_WRITE::SYS_OPEN::nil.

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
| os_open: forall ge z s m c md0 fname0 md fname unused_fd fs' sig,
  let fs := get_fs s in 
  at_external csem (get_core s) = Some (SYS_OPEN, sig, fname0::md0::nil) ->
  alloc_fd fs = Some unused_fd ->
  val2omode md0 = Some md -> 
  val2oint fname0 = Some fname -> 
  ~is_open fs fname -> 
  fs_open fs unused_fd fname md = Some fs' -> 
  after_external csem (Some (Vint unused_fd)) (get_core s) = Some c -> 
  os_step ge s m (mkxT z c fs') m
| os_read: forall ge z s m c fd0 fd buf adr nbytes0 nbytes bytes m' sig,
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_READ, sig, fd0::buf::nbytes0::nil) ->
  val2oint fd0 = Some fd -> 
  val2oadr buf = Some adr -> 
  val2oint nbytes0 = Some nbytes -> 
  fs_read fs fd (nat_of_Z (Int.unsigned nbytes)) = Some bytes -> 
  Mem.storebytes m (fst adr) (snd adr) bytes = Some m' -> 
  after_external csem (Some (Vint (Int.repr (Zlength bytes)))) (get_core s) = Some c -> 
  os_step ge s m (mkxT z c fs) m'
| os_write: forall ge z s m c fd0 fd adr buf nbytes0 nbytes bytes fs' nbytes_written sig,
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_WRITE, sig, fd0::buf::nbytes0::nil) ->
  val2oint fd0 = Some fd -> 
  val2oadr buf = Some adr -> 
  val2oint nbytes0 = Some nbytes -> 
  Mem.loadbytes m (fst adr) (snd adr) (Int.unsigned nbytes) = Some bytes -> 
  fs_write fs fd bytes = Some (nbytes_written, fs') -> 
  after_external csem (Some (Vint (Int.repr (Z_of_nat nbytes_written)))) (get_core s) = Some c -> 
  os_step ge s m (mkxT z c fs') m.

Definition os_initial_mem := sim.initial_mem csem.

Definition os_make_initial_core (ge: genv) (v: val) (args: list val): option xT :=
  match make_initial_core csem ge v args with
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

Definition os_after_external (ov: option val) (s: xT): option xT :=
  match after_external csem ov (get_core s) with
  | Some c => Some (mkxT (get_ext s) c (get_fs s))
  | None => None
  end.

Definition os_safely_halted (s: xT): option val :=
  safely_halted csem (get_core s).

Program Definition FSCoreSem := Build_CoreSemantics genv xT mem D
  os_initial_mem
  os_make_initial_core
  os_at_external
  os_after_external
  os_safely_halted
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
unfold os_at_external; rewrite H0; auto.
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H0; simpl; auto.
edestruct (at_external_halted_excl csem); eauto. congruence.
edestruct (at_external_halted_excl csem); eauto. congruence.
edestruct (at_external_halted_excl csem); eauto. congruence.
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
        Mem.range_perm m (fst adr) (snd adr) (snd adr + Int.unsigned nbytes) Cur Writable
    | _, _, _ => False
    end
  | SYS_WRITE, (fsys, z), (fd0::buf::nbytes0::nil) => 
    match val2oint fd0, val2oadr buf, val2oint nbytes0 with
    | Some fd, Some adr, Some nbytes => 
        u=adr /\
        List.Forall2 Val.has_type (fd0::buf::nbytes0::nil) (sig_args SYS_WRITE_SIG) /\
        is_writable fsys fd /\ 
        Mem.range_perm m (fst adr) (snd adr) (snd adr + Int.unsigned nbytes) Cur Readable
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
          Mem.loadbytes m (fst adr) (snd adr) (Int.unsigned nbytes) = Some bytes))
  | SYS_WRITE, (fsys, z) => True
  | _, _ => True
  end.

Definition Client_FSExtSpec :=
  Build_external_specification Memory.mem AST.external_function (fs*Z)
  (fun ef: AST.external_function => address) fs_pre fs_post.

Definition Client_FSExtSpec' :=
  Build_external_specification juicy_mem AST.external_function (fs*Z)
  (fun ef: AST.external_function => address) 
  (fun ef u typs args fsz jm => fs_pre ef u typs args fsz (m_dry jm)) 
  (fun ef u ty retval0 fsz jm => fs_post ef u ty retval0 fsz (m_dry jm)).

Program Definition Client_JuicyFSExtSpec := 
  Build_juicy_ext_spec (fs*Z) Client_FSExtSpec' _ _.
Next Obligation. 
hnf; intros a a' H. 
destruct e; auto.
destruct name; auto.
destruct name; auto.
destruct sg; auto.
destruct sig_args; auto.
destruct t0; auto.
destruct sig_args; auto.
destruct t0; auto.
destruct sig_args; auto.
destruct t0; auto.
destruct sig_args; auto.
destruct sig_res; auto.
destruct t0; auto.
destruct args; auto.
destruct args; auto.
destruct args; auto.
destruct args; auto.
destruct (val2oint v); auto.
destruct (val2oadr v0); auto.
destruct (val2oint v1); auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
Qed.
Next Obligation. 
hnf; intros a a' H; destruct e; auto. 
apply age_jm_dry in H.
rewrite <-H.
auto.
Qed.

Lemma empty_rmap_no (lev: nat) loc: 
  compcert_rmaps.R.resource_at (compcert_rmaps.RML.empty_rmap lev) loc = 
  compcert_rmaps.R.NO shares.Share.bot.
Proof.
unfold compcert_rmaps.RML.empty_rmap.
unfold compcert_rmaps.RML.empty_rmap'.
unfold compcert_rmaps.R.resource_at.
rewrite compcert_rmaps.R.unsquash_squash; simpl.
unfold compose; simpl; auto.
Qed.

Lemma exists_ok_rmap (m: mem) (lev: nat): 
  exists phi, initial_rmap_ok m phi /\ ageable.level phi=lev.
Proof.
exists (compcert_rmaps.RML.empty_rmap lev); split.
unfold initial_rmap_ok.
intros.
rewrite <-compcert_rmaps.RML.core_resource_at.
rewrite empty_rmap_no.
rewrite compcert_rmaps.RML.core_NO; auto.
apply compcert_rmaps.RML.empty_rmap_level.
Qed.

Lemma juicy_mem_exists (lev: nat) (m: mem): 
  exists jm, m_dry jm=m /\ ageable.level jm=lev.
Proof.
destruct (exists_ok_rmap m lev) as [phi [H1 H2]].
exists (initial_mem m phi H1).
split; auto.
simpl.
unfold inflate_initial_mem.
rewrite level_make_rmap.
auto.
Qed.

Lemma juicy_safeN_safeN ge n z c jm :
  safeN (juicy_core_sem csem) Client_JuicyFSExtSpec ge n z c jm -> 
  safeN csem Client_FSExtSpec ge n z c (m_dry jm).
Proof.
revert jm z c; induction n; auto.
intros jm z c H1.
hnf.
hnf in H1.
case_eq (at_external (juicy_core_sem csem) c).
intros [[ef sig] args] H2.
rewrite H2 in H1.
inv H2.
rewrite H0.
case_eq (safely_halted (juicy_core_sem csem) c).
intros rv H2.
rewrite H2 in H1.
elimtype False; auto.
intros H2.
rewrite H2 in H1.
inv H2.
unfold j_safely_halted in H3.
rewrite H3.
destruct H1 as [x [H1 H2]].
exists x.
split; auto.
intros ret m' z' H4.
destruct (juicy_mem_exists (ageable.level jm) m') as [jm' [H5 H6]].
specialize (H2 ret jm' z').
spec H2; auto.
simpl in H4|-*.
rewrite H5; auto.
destruct H2 as [c' [H2 H7]].
exists c'.
split; auto.
rewrite <-H5.
eapply IHn; eauto.
intros H2.
rewrite H2 in H1.
inv H2.
rewrite H0.
case_eq (safely_halted (juicy_core_sem csem) c).
intros rv H2.
rewrite H2 in H1.
inv H2.
unfold j_safely_halted in H3.
rewrite H3; auto.
intros H2.
rewrite H2 in H1.
inv H2.
unfold j_safely_halted in H3.
rewrite H3; auto.
destruct H1 as [c' [jm' [H1 H2]]].
exists c'; exists (m_dry jm').
split; auto.
inv H1.
auto.
Qed.

Variable FSExtSpec: ext_spec Z.
Variable FSExtSpec_linkable: linkable proj_zext handled Client_FSExtSpec FSExtSpec.
Variable ge: genv.

Import TruePropCoercion.

Program Definition fs_extension := 
  Extension.Make 
    _
    (fun _ => D)
    FSCoreSem
    cores
    Client_FSExtSpec
    FSExtSpec 
    handled
    (const 1)
    proj_core _
    active _ 
    proj_zint
    proj_zext
    zmult _ _ _ _  
   FSExtSpec_linkable.
Next Obligation. unfold proj_core. if_tac; auto. unfold const in *. 
 rewrite H0 in H; elimtype False; omega. Qed.
Next Obligation. unfold proj_core, active; if_tac; try congruence; eauto. Qed.
Next Obligation. 
unfold os_at_external in H1.
(*Next Obligation.
apply at_external_handled in H0.
unfold is_true; auto.
Qed.*)
simpl in H1.
unfold cores in H0; simpl in H0.
rewrite H0 in H1.
unfold is_true.
if_tac; auto.
if_tac; auto.
if_tac; auto.
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
Qed.
Next Obligation. (*this proof should be automated*)
if_tac; auto.
rewrite H0 in H.
unfold os_at_external in H.
destruct (at_external csem (get_core s)).
destruct p as [[ef' sig'] vals].
destruct ef'; try congruence.
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
destruct sig'; try congruence.
destruct sig_args; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_res0; try congruence.
destruct t; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_res0; try congruence.
destruct t; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct sig_res0; try congruence.
destruct t0; try congruence.
destruct sg; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_res0; try congruence.
destruct sig_args0; try congruence.
destruct t1; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
congruence.
if_tac.
unfold os_at_external in H.
destruct (at_external csem (get_core s)).
destruct p as [[ef' sig'] vals].
destruct ef'; try congruence.
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
congruence.
if_tac.
unfold os_at_external in H.
destruct (at_external csem (get_core s)).
destruct p as [[ef' sig'] vals].
destruct ef'; try congruence.
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
destruct sig'; try congruence.
destruct sig_args; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_res0; try congruence.
destruct t; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_res0; try congruence.
destruct t; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct sig_res0; try congruence.
destruct t0; try congruence.
destruct sg; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_res0; try congruence.
destruct sig_args0; try congruence.
destruct t1; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
destruct t0; try congruence.
destruct sig_args0; try congruence.
congruence.
unfold os_at_external in H.
destruct (at_external csem (get_core s)).
destruct p as [[ef' sig'] vals].
destruct ef'; try congruence.
congruence.
Qed.
Next Obligation.
unfold os_after_external in H0.
destruct (after_external csem ret (get_core s)); try congruence.
inv H0; auto.
Qed.

Lemma mem_range_perm_sub m b ofs sz sz' k p :
  Mem.range_perm m b ofs sz' k p -> 
  (sz <= sz')%Z -> 
  Mem.range_perm m b ofs sz k p.
Proof.
unfold Mem.range_perm.
intros H1 H2.
intros ofs' H3.
specialize (H1 ofs').
spec H1.
omega.
auto.
Qed.

Import ExtensionSafety.

Lemma fs_extension_safe (csem_fun: corestep_fun csem): 
 safe_extension ge (fun _:nat => ge) fs_extension.
Proof.
destruct (ExtensionSafety fs_extension ge (fun _:nat => ge)) as [PF00].
apply PF00; constructor.

(*1: core preservation of all-safety invariant*)
intros until m'; intros H1 (*H2*) H4 H5 H6.
assert (H3:True) by auto.
assert (get_core s'=c').
 clear -H4 H5 H6 csem_fun.
 unfold cores in H5.
 simpl in H4.
 inversion H6; subst; simpl in *.
 unfold active, proj_core in H4; simpl in H4.
 inv H4.
 generalize (csem_fun _ _ _ _ _ _ _ H5 H); inversion 1; auto.
 apply corestep_not_at_external in H5.
 unfold active, proj_core in H4.
 if_tac in H4; try congruence.
 apply corestep_not_at_external in H5.
 unfold active, proj_core in H4.
 if_tac in H4; try congruence.
 apply corestep_not_at_external in H5.
 unfold active, proj_core in H4.
 solve[if_tac in H4; try congruence].
rewrite <-H in *.
hnf.
intros i2 c2 H8.
assert (H7:True) by auto.
hnf in H1.
specialize (H1 (active s) c).
spec H1; auto.
unfold cores.
clear H3.
assert (H3: c'=c2).
 destruct s'.
 simpl in H.
 rewrite <-H.
 inversion H8.
 unfold proj_core in H2.
 if_tac in H2; try congruence.
 solve[inversion H2; auto].
rewrite <-H3 in *.
rewrite <-H.
eapply safe_corestep_forward; eauto.
assert (H2: Extension.zmult fs_extension (Extension.proj_zint fs_extension s') =
            Extension.zmult fs_extension (Extension.proj_zint fs_extension s)).
 clear - H4 H5 H6.
 inversion H4.
 inv H0.
 inv H6; auto.
 elimtype False.
  apply corestep_not_at_external in H5.
  unfold cores, Extension.active in H5.
  solve[rewrite H5 in H; congruence].
 elimtype False.
  apply corestep_not_at_external in H5.
  unfold cores, Extension.active in H5.  
  solve[rewrite H5 in H; congruence].
unfold SafetyInvariant.proj_zint.
unfold cores in H2.
solve[rewrite H2; auto].

(*2: core progress*)
intros until c; intros H1 H2 (*H3*) H5.
assert (H4:True).
hnf in H1.
specialize (H1 (active s) c).
spec H1; auto.
inversion H5.
inv H0.
simpl in H2; unfold runnable in H2.
hnf in H1.
simpl in H5.
destruct s; simpl in H2.
specialize (H1 (active (mkxT z0 c fs0)) c).
simpl in H1.
unfold rg_sim.runnable in H3.
unfold active, cores in *.
spec H1; auto.
destruct (at_external csem c) as [[[ef sig] args]|]; try congruence.
destruct (safely_halted csem c); try congruence.
destruct H1 as [c' [m' [H1 H6]]].
exists c'; exists (mkxT z0 c' fs0); exists m'.
split; auto.
split; auto.
unfold proj_core in H2.
if_tac in H2; try congruence.
simpl in H2.
inv H2.
solve[apply os_corestep; auto].

(*3: handled steps respect function specs.*)
intros until x.
hnf; intros H2 H3 H4 H5 Hpre Hstep H7.
assert (H1:True) by auto.
assert (H6:True) by auto.
inv H2.
inversion Hstep.
rewrite <-H8, <-H9, <-H10 in *.
clear H8 H9 H10.
(*corestep case; impossible*)
elimtype False.
apply corestep_not_at_external in H.
simpl in H3.
unfold cores, active, get_core in H3.
destruct s; auto.
inv H2.
solve[rewrite H in H3; congruence].
(*SYS_OPEN case*)
assert (Hef: ef = SYS_OPEN).
 clear - H H3.
 unfold cores, active, get_core in H3.
 destruct s; auto.
 simpl in H.
 rewrite H in H3.
 solve[inversion H3; auto].
rewrite Hef in *.
right.
exists (Some (Vint unused_fd)).
rewrite <-H15 in H7.
split; auto.
simpl.
unfold cores, active; auto.
rewrite H11.
f_equal.
simpl in H7.
unfold proj_core, active in H7.
if_tac in H7; try congruence.
inversion H7; auto.
simpl.
unfold spec_of in H5.
clear H12.
rename H10 into H12.
clear - H5 H12.
(*inversion H5 fails to terminate in a timely fashion; instead we 
   use this ad hoc lemma*)
assert (forall {A B: Type} (P P': A) (Q Q': B), (P,Q) = (P',Q') -> P=P' /\ Q=Q').
 solve[inversion 1; auto].
apply H in H5.
destruct H5 as [H5 H6].
rewrite <-H6.
hnf; unfold fs_post; simpl; auto.
unfold fs_open in H12.
if_tac in H12.
case_eq (get_fstore fs0 fname).
intros f H1; rewrite H1 in H12.
inversion H12; subst.
hnf.
exists md; exists 0; exists f.
unfold get_fdtable, get_fcache, fs_open_existing; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
intros H1; rewrite H1 in H12.
inversion H12; subst.
hnf.
unfold get_fdtable, get_fcache, fs_open_existing; simpl.
exists md; exists 0; exists new_file.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
hnf.
destruct (get_fstore fs0 fname).
inversion H12; subst.
exists md; exists 0; exists f.
unfold get_fdtable, get_fcache; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
congruence.
(*SYS_READ case*)
assert (Hef: ef = SYS_READ).
 unfold cores, Extension.active in H3.
 solve[rewrite H in H3; inversion H3; auto].
right.
exists (Some (Vint (Int.repr (Zlength bytes)))).
split; auto.
simpl.
unfold spec_of in H5.
rewrite Hef in *.
unfold cores, active.
rewrite <-H15 in H7.
simpl in H7.
unfold proj_core, active in H7.
if_tac in H7; try congruence.
inversion H7.
rewrite H11.
solve[auto].
assert (Heq: x = adr).
 unfold cores, Extension.active in H3.
 rewrite H in H3.
 inversion H3.
 rewrite <-H20 in *.
 inversion H5; subst.
 simpl in Hpre.
 rewrite H0, H2, H8 in Hpre.
 solve[destruct Hpre; auto].
clear -Heq Hef H5 H9 H10 H11.
assert (forall {A B: Type} (P P': A) (Q Q': B), (P,Q) = (P',Q') -> P=P' /\ Q=Q').
 solve[inversion 1; auto].
apply H in H5.
destruct H5 as [H5 H6].
rewrite <-H6.
simpl; auto.
rewrite Hef.
remember (Int.repr (Zlength bytes)) as N.
simpl.
exists bytes.
split; auto.
apply Mem.loadbytes_storebytes_same in H10.
rewrite Zlength_correct in HeqN.
assert (Hlen: (0 <= Z_of_nat (length bytes) < Int.modulus)%Z).
 split.
 apply Zle_0_nat; auto.
 unfold fs_read in H9.
 destruct (get_file fs0 fd); try congruence.
 destruct (get_fptr fs0 fd); try congruence.
 unfold read_file in H9.
 inversion H9.
 generalize (read_file_aux_length f (nat_of_Z (Int.unsigned nbytes)) (get_size f) f0);
  intro H2.
 apply Zle_lt_trans with (m := Int.unsigned nbytes).
 apply inj_le in H2.
 rewrite nat_of_Z_eq in H2; auto.
 destruct nbytes as [? [Pf1 Pf2]]; simpl in *; omega.
 destruct nbytes as [? [Pf1 Pf2]]; simpl in *; omega.
 change (Int.unsigned N) with (Int.unsigned N).
 subst N x; rewrite Int.unsigned_repr; auto.
 unfold Int.max_unsigned; omega.
(*SYS_WRITE case*)
right.
exists (Some (Vint (Int.repr (Z_of_nat nbytes_written)))).
split; auto.
rewrite <-H15 in H7.
simpl in H7.
unfold proj_core, active in H7.
if_tac in H7; try congruence.
inversion H7.
unfold cores, active.
solve[rewrite H11; auto].
simpl.
unfold spec_of in H5.
assert (Hef: ef = SYS_WRITE).
 unfold cores, Extension.active in H3.
 rewrite H in H3.
 solve[inversion H3; auto].
clear - Hef H5.
rewrite Hef in *.
assert (forall {A B: Type} (P P': A) (Q Q': B), (P,Q) = (P',Q') -> P=P' /\ Q=Q').
 inversion 1; auto.
apply H in H5.
destruct H5 as [H5 H6].
rewrite <-H6.
solve[simpl; auto].

(*4: handled progress*)
intros until c; intros H1 H2 H3.
inv H2.
unfold safely_halted.
simpl.
unfold os_safely_halted.
hnf in H1.
specialize (H1 (active s) (get_core s)).
spec H1; auto.
hnf in H1.
rename H3 into H0.
unfold rg_sim.runnable in H0.
case_eq (at_external csem (get_core s)). 
intros [[ef sig] args] Hat.
(*at_external core = Some*)
unfold cores, active in H1.
rewrite Hat in *.
destruct (safely_halted csem (get_core s)).
solve[elimtype False; auto].
destruct H1 as [x [H1 H2]].
left.
destruct ef; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct sg; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct sig_res; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
simpl in H1.
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oadr v0); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v1); try solve[elimtype False; simpl in H1; auto].
intros.
rewrite H3, H4, H5 in H1.

(*SYS_READ case*)
destruct H1 as [Heq [H1 [H6 H7]]].
unfold proj_zint in H6.
destruct H6 as [md [cur [f' [H6 H8]]]].
apply mem_range_perm_sub with 
 (sz := (snd a + Z_of_nat (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) 
                             (get_size f') cur)))%Z)
 in H7.
destruct a as [b ofs].
simpl in H7.
apply Mem.range_perm_storebytes in H7.
destruct H7 as [m' H7].
specialize (H2 
  (Some (Vint
    (Int.repr
      (Zlength
        (read_file_aux f' (nat_of_Z (Int.unsigned i)) 
          (get_size f') cur)))))
  m'
  (get_fs s, z)).
spec H2.
 case_eq (eq_nat_dec
 (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur))
 (nat_of_Z (Int.unsigned i))).
intros Heq'.
exists (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur).
split; auto.
apply Mem.loadbytes_storebytes_same in H7.
rewrite Zlength_correct.
rewrite Heq' in H7|-*.
destruct x; inv Heq.
rewrite Int.unsigned_repr. unfold fst, snd; auto.
rewrite nat_of_Z_eq.
 apply Int.unsigned_range_2.
 destruct (Int.unsigned_range_2 i); omega.
intros Hneq.
assert (H11: 
  length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur) <
  nat_of_Z (Int.unsigned i)).
 generalize (read_file_aux_length f' 
             (nat_of_Z (Int.unsigned i)) (get_size f') cur); intro H12.
 omega.
intros _.
exists (read_file_aux f' 
 (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur)) 
 (get_size f') cur).
apply Mem.loadbytes_storebytes_same in H7.
repeat rewrite Zlength_correct.
destruct x; inv Heq.
rewrite <-read_file_aux_length2; auto.
split; auto.
rewrite Int.unsigned_repr. unfold fst, snd.
rewrite <- read_file_aux_id.
auto.
split. omega.
clear - H11.
forget (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur)) as N.
apply inj_lt_iff in H11.
 destruct (Int.unsigned_range_2 i).
rewrite nat_of_Z_eq in H11; omega.

destruct H2 as [c' [H9 H10]].
exists (mkxT z c' (get_fs s)); exists m'.
split.
eapply os_read; eauto.
unfold fs_read.
unfold get_file.
unfold FSExtension.proj_zint in H6, H8.
rewrite H8.
unfold get_fptr.
rewrite H6.
eauto.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
unfold proj_core in H2.
if_tac in H2; try congruence.
inv H2.
solve[auto].
intros.
elimtype False.
unfold proj_core in H2.
if_tac in H2; try congruence.
apply (after_at_external_excl csem) in H9.
unfold cores in *.
inversion H2.
rewrite H15 in *.
clear H15.
rewrite H9 in H12.
congruence.
apply Zplus_le_compat_l.
assert (H9: 
 length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur) <=
 nat_of_Z (Int.unsigned i)).
 apply read_file_aux_length.
assert (H10: (Z_of_nat (nat_of_Z (Int.unsigned i)) <= Int.unsigned i)%Z).
 rewrite nat_of_Z_max.
 rewrite Z.max_lub_iff.
 split; auto.
 apply Zle_refl.
 apply Int.intrange.
apply Zle_trans with (m := Z_of_nat (nat_of_Z (Int.unsigned i))); auto.
apply inj_le; auto.
(*degenerate cases*)
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
intros ? H6; rewrite H6 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
solve[elimtype False; auto].

destruct name; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct sg; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct sig_res; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].

(*SYS_OPEN case*)
hnf in H1.
case_eq (val2oint v); try solve[elimtype False; simpl in H1; auto].
case_eq (val2omode v0); try solve[elimtype False; simpl in H1; auto].
intros md H4 fname H5.
rewrite H4, H5 in H1.
destruct H1 as [H1 [H6 H7]].
apply alloc_fd_success in H6.
destruct H6 as [unused_fd H6].
case_eq (file_exists (proj_zint fs_extension s) fname).
(*file exists*)
intros H8.
generalize H8 as H8'; intro.
generalize H8 as H8''; intro.
unfold file_exists in H8'.
case_eq (get_fstore (proj_zint fs_extension s) fname).
intros f H9.
specialize (H2 (Some (Vint unused_fd)) m 
 (fs_open_existing (proj_zint fs_extension s) unused_fd fname f md, z)).
spec H2; simpl; auto.
unfold is_readable.
exists md; exists 0; exists f; split.
unfold get_fdtable, fs_open_existing; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
unfold get_fcache, fs_open_existing; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
destruct H2 as [c' [H2 H10]].
exists (mkxT z c' (fs_open_existing (proj_zint fs_extension s) unused_fd fname f md)).
exists m.
split.
destruct H7 as [H7 H11].
eapply os_open; eauto.
unfold fs_open.
unfold proj_zint in H9.
unfold SafetyInvariant.proj_zint in H9.
simpl in H9.
unfold FSExtension.proj_zint in H9.
rewrite H9; auto.
if_tac; auto.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
rename H3 into H11.
assert (H3:True) by auto.
unfold proj_core in H11.
if_tac in H11; try congruence.
inv H11.
auto.
intros.
elimtype False.
rename H3 into H14.
assert (H3:True) by auto.
unfold proj_core in H14.
if_tac in H14; try congruence.
apply after_at_external_excl in H2.
unfold cores in *.
rewrite H2 in H12.
congruence.
(*degenerate case*)
intros H9.
unfold file_exists in H8''.
rewrite H9 in H8''.
simpl in H8''; congruence.
(*file doesn't yet exist*)
intros H8.
generalize H8 as H8'; intro.
generalize H8 as H8''; intro.
case_eq (get_fstore (proj_zint fs_extension s) fname).
intros f H9.
elimtype False.
unfold file_exists in H8.
rewrite H9 in H8.
simpl in H8; congruence.
intros H9.
specialize (H2 (Some (Vint unused_fd)) m 
 (fs_open_new (proj_zint fs_extension s) unused_fd fname md, z)).
spec H2; simpl; auto.
unfold is_readable.
exists md; exists 0.
unfold get_fdtable, get_fcache, fs_open_new; simpl.
case_eq (Int.eq unused_fd unused_fd).
intros; exists new_file; split; auto.
rewrite Int.eq_true; congruence.
destruct H2 as [c' [H2 H10]].
exists (mkxT z c' (fs_open_new (proj_zint fs_extension s) unused_fd fname md)).
exists m.
split.
destruct H7 as [H7 H11].
eapply os_open; eauto.
unfold fs_open.
unfold proj_zint in H9.
unfold SafetyInvariant.proj_zint in H9.
simpl in H9.
unfold FSExtension.proj_zint in H9.
rewrite H9; auto.
case_eq (fwritable md); auto.
intros H12.
rewrite H12 in H7.
elimtype False.
spec H7.
unfold file_exists; intros H13.
unfold SafetyInvariant.proj_zint in H13.
simpl in H13.
unfold FSExtension.proj_zint in H13.
rewrite H9 in H13.
simpl in H13; congruence.
congruence.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
rename H3 into H11.
assert (H3:True) by auto.
unfold proj_core in H11.
if_tac in H11; try congruence.
inv H11.
auto.
intros.
elimtype False.
rename H3 into H14.
assert (H3:True) by auto.
unfold proj_core in H14.
if_tac in H14; try congruence.
apply after_at_external_excl in H2.
unfold cores in H13.
inversion H13.
inv H14.
unfold cores in *.
rewrite H2 in H12.
congruence.
(*degenerate cases*)
intros H9 i H4.
rewrite H4, H9 in H1.
elimtype False; auto.
intros H4.
rewrite H4 in H1.
solve[elimtype False; auto].

destruct sg; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct sig_res; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
simpl in H1.
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oadr v0); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v1); try solve[elimtype False; simpl in H1; auto].
intros.
rewrite H3, H4, H5 in H1.

(*SYS_WRITE case*)
destruct H1 as [Heq [H1 [H6 H7]]].
unfold proj_zint in H6.
destruct H6 as [md [cur [f' [H6 [H8 H80]]]]].
destruct a as [b ofs].
simpl in H7.
apply Mem.range_perm_loadbytes in H7.
destruct H7 as [bytes H7].
assert (H9: exists nbytes_written, exists fsys', 
  fs_write (get_fs s) i0 bytes = Some (nbytes_written, fsys')).
  unfold fs_write, get_file, get_fptr, get_fmode.
  unfold FSExtension.proj_zint in H6, H80.
  rewrite H6, H8, H80.
  case_eq (write_file f' cur bytes).
  intros fsys' nbytes_written H9.
  exists nbytes_written. 
  eexists; eauto.
destruct H9 as [nbytes_written [fsys' H90]].
specialize (H2 (Some (Vint (Int.repr (Z_of_nat nbytes_written)))) m (fsys', z)).
spec H2; simpl; auto.
destruct H2 as [c' [H9 H10]].
exists (mkxT z c' fsys'); exists m.
split.
eapply os_write 
 with (nbytes := Int.repr (Z_of_nat nbytes_written)); eauto.
rewrite H3.
f_equal.
apply Mem.loadbytes_length in H7.
apply fs_write_length in H90.
rewrite H90.
rewrite H7.
rewrite nat_of_Z_eq.
generalize (Int.repr_unsigned i).
unfold Int.unsigned; auto.
destruct (Int.intrange i). destruct (Int.unsigned_range_2 i); omega.
unfold fst, snd.
generalize H7 as H7'.
apply Mem.loadbytes_length in H7.
apply fs_write_length in H90.
rewrite H90.
rewrite H7.
rewrite nat_of_Z_eq.
rewrite Int.repr_unsigned; auto.
destruct (Int.unsigned_range_2 i); omega.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
rename H2 into H11.
assert (H2:True) by auto.
unfold proj_core in H11.
if_tac in H11; try congruence.
inv H11.
auto.
intros.
elimtype False.
rename H2 into H13.
assert (H2:True) by auto.
unfold proj_core in H13.
if_tac in H13; try congruence.
apply after_at_external_excl in H9.
unfold cores in H2.
unfold cores in *.
rewrite H9 in H12.
congruence.
(*degenerate cases*)
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
intros ? H6; rewrite H6 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
elimtype False; auto.
intros H4.
unfold cores, active in H1. 
unfold cores, Extension.active in H0.
rewrite H4 in H0, H1.
(*safely halted*)
destruct (safely_halted csem (get_core s)); try congruence.
solve[right; exists v; auto].

(*5: safely halted threads remain halted*)
intros until rv; intros H2 H3 H4.
assert (H1:True) by auto.
unfold cores in H1.
simpl in H2.
unfold proj_core in H2.
if_tac in H2; try congruence.
inv H2.
unfold cores in *.
inv H4.
apply corestep_not_halted in H.
simpl in H3.
rewrite H in H3; congruence.
destruct (at_external_halted_excl csem (get_core s)).
rewrite H4 in H; congruence.
rewrite H4 in H3; congruence.
destruct (at_external_halted_excl csem (get_core s)).
rewrite H4 in H; congruence.
rewrite H4 in H3; congruence.
destruct (at_external_halted_excl csem (get_core s)).
rewrite H4 in H; congruence.
solve[rewrite H4 in H3; congruence].

(*6: safety of other cores preserved over handled steps*)
intros until c; hnf.
intros [H1 H2].
intros H3 j c2 H6.
split.
intros H8.
simpl in H8.
unfold proj_core in H8.
if_tac in H8; try congruence.
rewrite H in H6.
simpl in H6.
unfold active in H6.
solve[elimtype False; auto].
intros n z z' H8 H9.
simpl in H8.
unfold proj_core in H8.
if_tac in H8; try congruence.
rewrite H in H6.
simpl in H6.
unfold active in H6.
solve[elimtype False; auto].

(*7: extended machine doesn't introduce new external calls*)
intros until args; intros H1.
inv H1.
case_eq (at_external csem (get_core s)).
intros [[ef' sig'] args'] H1.
exists (get_core s).
split; auto.
unfold os_at_external in H0|-*.
rewrite H1 in H0|-*.
unfold cores in *.
destruct ef'; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_res; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_args; try congruence.
destruct sig_args; try congruence.
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
intros H1.
unfold os_at_external in H0.
solve[rewrite H1 in H0; congruence].

(*8: *)
intros.
simpl.
unfold os_after_external.
unfold cores in *.
inversion H.
subst.
simpl in *.
unfold proj_core in *.
if_tac in H; try congruence.
inv H.
rewrite H4.
solve[eexists; eauto].

(*9: *)
intros.
split; auto.
intros H9.
assert (H8:True) by auto.
simpl in H9.
unfold proj_core in H9.
if_tac in H9; auto.
rewrite H10 in H7.
rename H6 into H11.
simpl in H11.
unfold proj_core in H11.
if_tac in H11; try congruence.
simpl in H7.
congruence.
congruence.
rename H into H8.
simpl in H8.
unfold proj_core in H8.
if_tac in H8; try congruence.
subst.
intros ge' n H13 H14.
simpl in H13.
unfold proj_core in H13.
if_tac in H13; try congruence.
simpl in H7.
congruence.
Qed.

End FSExtension.
