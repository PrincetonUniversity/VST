Load loadpath.
Require Import msl.base 
               veric.sim veric.step_lemmas veric.base veric.expr
               veric.extensions veric.extspec veric.null_extension
               veric.juicy_mem veric.juicy_extspec veric.Address.

Set Implicit Arguments.

Inductive f_mode: Type := RDONLY | WRONLY | RDWR.

Definition f_writable (mode: f_mode) :=
  match mode with
  | RDONLY => false
  | WRONLY => true
  | RDWR => true
  end.

Inductive file: Type := mkfile: forall 
  (mode: f_mode) (sz: nat) (cur: nat) (contents: forall (ofs: nat), memval), file.

Inductive fsys: Type := mkfsys: 
  forall (fdtable: forall (fd: int), option file) (nopen: nat) (next_fd: int), fsys.

Section selectors.
Variable (fs: fsys).
Definition get_fdtable := match fs with mkfsys fdtable _ _ => fdtable end.
Definition get_nopen := match fs with mkfsys _ nopen _ => nopen end.
Definition get_next_fd := match fs with mkfsys _ _ fd => fd end.

Variable (fd: int).
Definition get_file := get_fdtable fd.

Variable (f: file).
Definition get_mode := match f with mkfile mode _ _ _ => mode end.
Definition get_sz := match f with mkfile _ sz _ _ => sz end.
Definition get_cur := fun f => match f with mkfile _ _ cur _ => cur end.
Definition get_contents := fun f => match f with mkfile _ _ _ contents => contents end.

End selectors.

Definition empty_fs := mkfsys (fun _:int => None).

Section FSExtension.
Variables 
  (Z cT D: Type) 
  (csem: CoreSemantics genv cT mem D)
  (client_sig: ext_sig mem fsys)

  (after_at_external_excl: forall c ret c',
    after_external csem ret c = Some c' -> at_external csem c' = None)
  (at_external_handled: forall c ef args sig,
    at_external csem c = Some (ef, sig, args) -> IN ef client_sig = true)

  (init_world: Z).

Definition cores := fun _:nat => Some csem.

Local Open Scope nat_scope.

Inductive xT: Type := mkxT: forall (z: Z) (c: cT) (fs: fsys), xT.

Section selectors.
Variable (s: xT).

Definition get_ext := match s with mkxT z _ _ => z end.
Definition get_core := match s with mkxT _ c _ => c end.
Definition get_fs := match s with mkxT _ _ fs => fs end.

End selectors.

Definition proj_core (s: xT) (i: nat) := if eq_nat_dec i 1 then Some (get_core s) else None.
Definition active := fun _: xT => 1.
Definition runnable := fun (ge: genv) (s: xT) => 
  match at_external csem (get_core s), safely_halted csem ge (get_core s) with 
  | None, None => Some 1
  | _, _ => None
  end.
Definition proj_zint := get_fs.
Definition proj_zext := get_ext.
Definition zmult := @prod Z fsys. 

Notation SYS_READ_SIG := (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation SYS_WRITE_SIG := (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation SYS_OPEN_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).

Notation SYS_READ := (EF_external 3%positive SYS_READ_SIG).
Notation SYS_WRITE :=  (EF_external 4%positive SYS_WRITE_SIG).
Notation SYS_OPEN := (EF_external 8%positive SYS_OPEN_SIG).

Definition int2f_mode (i: int): option f_mode := 
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
  | Vptr b ofs => Some (b, Int.intval ofs)
  end.

Definition val2omode (mode: val): option f_mode :=
  match val2oint mode with Some i => int2f_mode i | None => None end.

Section read_write.
Variable (f: file).

Let contents := get_contents f.

Fixpoint read_file_aux (nbytes sz cur: nat): list memval :=
  match nbytes with 
  | O => nil
  | S nbytes' => if eq_nat_dec sz cur then nil 
                 else contents cur :: read_file_aux nbytes' sz (S cur)
  end.

Definition read_file (nbytes: nat): file*list memval :=
  let bytes := read_file_aux nbytes (get_sz f) (get_cur f) in
  (mkfile (get_mode f) (get_sz f) (get_cur f + length bytes) (get_contents f), bytes).

Fixpoint write_file_aux (bytes: list memval) (sz cur: nat): (nat -> memval)*nat :=
  match bytes with 
  | nil => (contents, O)
  | byte::bytes' => 
    match write_file_aux bytes' sz (S cur) with (contents', nbytes) => 
        (fun ofs => if eq_nat_dec ofs cur then byte else contents' ofs, S nbytes)
    end
  end.

Definition write_file (bytes: list memval): file*nat :=
  match write_file_aux bytes (get_sz f) (get_cur f) with (contents, nwritten) => 
    (mkfile (get_mode f) (get_sz f + (get_cur f + nwritten - get_sz f)) 
            (get_cur f + nwritten) (get_contents f), 
     nwritten)
  end.

End read_write.

Section alloc_fd.
Variable (fs: fsys).

Fixpoint find_unused_fd (n: nat) (fdtable: int -> option file) :=
  match n with 
  | O => None
  | S n' => match fdtable (Int.repr (Z_of_nat n)) with 
            | None => Some (Int.repr (Z_of_nat n))
            | Some _ => find_unused_fd n' fdtable
            end
  end.

Definition alloc_fd := 
   match get_file fs (get_next_fd fs) with
   | None => Some (get_next_fd fs)
   | Some _ => find_unused_fd (nat_of_Z Int.modulus) (get_fdtable fs)
   end.

End alloc_fd.

Definition handled: list AST.external_function := SYS_READ::SYS_WRITE::SYS_OPEN::nil.

Inductive os_step: genv -> xT -> mem -> xT -> mem -> Prop :=
| os_corestep: forall ge s m s' m',
  get_fs s=get_fs s' -> 
  get_ext s=get_ext s' -> 
  corestep csem ge (get_core s) m (get_core s') m' -> 
  os_step ge s m s' m'
| os_open: forall ge z s m c mode unused_fd fmode,
  let fs := get_fs s in 
  alloc_fd fs = Some unused_fd -> 
  at_external csem (get_core s) = Some (SYS_OPEN, SYS_OPEN_SIG, mode::nil) ->
  after_external csem (Some (Vint (get_next_fd fs))) (get_core s) = Some c -> 
  val2omode mode = Some fmode -> 
  let new_file := mkfile fmode O O (fun _:nat => Undef) in
  os_step ge s m (mkxT z c 
    (mkfsys (fun fd => if Int.eq fd unused_fd then Some new_file else get_fdtable fs fd)
            (S (get_nopen fs))
            (Int.add unused_fd Int.one))) m
| os_read: forall ge z s m c fd fd' adr buf nbytes nbytes' file file' bytes m',
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_READ, SYS_READ_SIG, fd::buf::nbytes::nil) ->
  val2oint fd = Some fd' -> 
  val2oadr buf = Some adr -> 
  val2oint nbytes = Some nbytes' -> 
  get_file fs fd' = Some file -> 
  read_file file (nat_of_Z (Int.intval nbytes')) = (file', bytes) -> 
  Mem.storebytes m (fst adr) (snd adr) bytes = Some m' -> 
  after_external csem (Some (Vint (Int.repr (Zlength bytes)))) (get_core s) = Some c -> 
  os_step ge s m (mkxT z c
    (mkfsys (fun fd => if Int.eq fd fd' then Some file' else get_file fs fd)
            (get_nopen fs)
            (get_next_fd fs))) m'
| os_write: forall ge z s m c fd fd' adr buf nbytes nbytes' nwritten file file' bytes,
  let fs := get_fs s in
  at_external csem (get_core s) = Some (SYS_WRITE, SYS_WRITE_SIG, fd::buf::nbytes::nil) ->
  val2oint fd = Some fd' -> 
  val2oadr buf = Some adr -> 
  val2oint nbytes = Some nbytes' -> 
  get_file fs fd' = Some file -> 
  f_writable (get_mode file) = true -> 
  Mem.loadbytes m (fst adr) (snd adr) (Int.intval nbytes') = Some bytes -> 
  write_file file bytes = (file', nwritten) -> 
  after_external csem (Some (Vint (Int.repr (Z_of_nat nwritten)))) (get_core s) = Some c -> 
  os_step ge s m (mkxT z c
    (mkfsys (fun fd => if Int.eq fd fd' then Some file' else get_file fs fd)
            (get_nopen fs)
            (get_next_fd fs))) m.

Definition os_initial_mem := sim.initial_mem csem.

Definition initial_fs: fsys := mkfsys (fun _:int => None) O Int.zero.

Definition os_make_initial_core (ge: genv) (v: val) (args: list val): option xT :=
  match make_initial_core csem ge v args with
  | Some c => Some (mkxT init_world c initial_fs)
  | None => None
  end.

Definition os_at_external (s: xT) :=
  match at_external csem (get_core s) with
  | Some (SYS_READ, SYS_READ_SIG, args) => None
  | Some (SYS_WRITE, SYS_WRITE_SIG, args) => None
  | Some (SYS_OPEN, SYS_OPEN_SIG, args) => None
  | Some (ef, sig, args) => Some (ef, sig, args)
  | None => None
  end.

Definition os_after_external (ov: option val) (s: xT): option xT :=
  match after_external csem ov (get_core s) with
  | Some c => Some (mkxT (get_ext s) c (get_fs s))
  | None => None
  end.

Definition os_safely_halted (ge: genv) (s: xT): option int :=
  safely_halted csem ge (get_core s).

Program Definition FSCoreSem := Build_CoreSemantics genv xT mem D
  os_initial_mem
  os_make_initial_core
  os_at_external
  os_after_external
  os_safely_halted
  os_step
  _ _ _.
Next Obligation.
case_eq (at_external csem (get_core q)).
2: unfold os_at_external; intros H1; rewrite H1; auto.
intros [[ef sig] args] H1.
inv H.
apply corestep_not_at_external in H3; congruence.
unfold os_at_external; rewrite H2; auto.
unfold os_at_external; rewrite H0; auto.
unfold os_at_external; rewrite H0; auto.
Qed.
Next Obligation.
inv H.
apply corestep_not_halted in H2.
unfold os_safely_halted; rewrite H2; auto.
edestruct (at_external_halted_excl csem); eauto. congruence.
edestruct (at_external_halted_excl csem); eauto. congruence.
edestruct (at_external_halted_excl csem); eauto. congruence.
Qed.
Next Obligation.
edestruct (at_external_halted_excl csem); eauto.
left; unfold os_at_external; rewrite H; auto.
Qed.

Definition JuicyFSCoreSem := juicy_core_sem FSCoreSem.

Definition Client_FSExtSpec :=
  Build_external_specification juicy_mem AST.external_function (Z*fsys)
  (fun ef: AST.external_function => unit (*placeholder for now*))
  (fun (ef: AST.external_function) u typs args zfs jm => 
    match ef, zfs with
      SYS_OPEN, (z, fs) => get_nopen fs < nat_of_Z Int.modulus 
    | _, (_, _) => False (*TODO*)
    end)
  (fun (ef: AST.external_function) u ty retval zfs jm => 
    match ef, zfs with
    | SYS_OPEN, (z, fs) => get_nopen fs < nat_of_Z Int.modulus 
    | _, (_, _) => False (*TODO*)
    end).

Program Definition Client_JuicyFSExtSpec := 
  Build_juicy_ext_spec (Z*fsys) Client_FSExtSpec _ _.
Next Obligation. hnf; intros a a' H; destruct e; auto. Qed.
Next Obligation. hnf; intros a a' H; destruct e; auto. Qed.

End FSExtension.
