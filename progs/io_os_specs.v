Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import Decimal.
Require Import List.
Require Import ZArith.
Open Scope Z.

(** Utils *)
Definition zle_le :
  forall x y z : Z, {x <= y <= z} + {x > y \/ y > z}.
Proof.
  intros; destruct (zle x y); auto.
  destruct (zle y z); auto.
Defined.

Fixpoint replace {A} (a : A) (n : nat) (l : list A) :=
  match n, l with
  | O, c :: tl => a :: tl
  | _, nil => nil
  | S n', c :: tl => c :: replace a n' tl
  end.

Definition enumerate {A} (xs : list A) : list (nat * A) := combine (seq 0 (length xs)) xs.

(** Datatypes *)
Module FlatMem.

  Local Notation "a # b" := (ZMap.get b a) (at level 1).

  Inductive flatmem_val :=
    | HUndef
    | HByte : byte -> flatmem_val.

  Definition flatmem := ZMap.t flatmem_val.

  Definition empty_flatmem : flatmem := ZMap.init HUndef.

  Definition FlatMem2MemVal (hv : flatmem_val) : memval :=
    match hv with
    | HUndef => Undef
    | HByte b => Byte b
    end.

  Fixpoint getN (n : nat) (p : Z) (c : flatmem) : list memval :=
    match n with
    | O => nil
    | S n' => FlatMem2MemVal c#p :: getN n' (p + 1) c
    end.

  Definition load (chunk : memory_chunk) (h : flatmem) (addr : Z) : val :=
    decode_val chunk (getN (size_chunk_nat chunk) addr h).

  Definition loadv (chunk : memory_chunk) (h : flatmem) (addr : val) : option val :=
    match addr with
    | Vint n => Some (load chunk h (Int.unsigned n))
    | _ => None
    end.

  Definition loadbytes (h : flatmem) (addr n : Z) : (list memval) :=
    getN (Z.to_nat n) addr h.

  Definition Mem2FlatMemVal (mv : memval) : flatmem_val :=
    match mv with
    | Byte b => (HByte b)
    | _ => HUndef
    end.

  Fixpoint setN (vl : list memval) (p : Z) (c : flatmem) : flatmem :=
    match vl with
    | nil => c
    | v :: vl' => setN vl' (p + 1) (ZMap.set p (Mem2FlatMemVal v) c)
    end.

  Definition store (chunk : memory_chunk) (h : flatmem) (addr : Z) (v : val) : flatmem :=
    setN (encode_val chunk v) addr h.

  Definition storev (chunk : memory_chunk) (h : flatmem) (addr v : val) : option flatmem :=
    match addr with
    | Vint n => Some (store chunk h (Int.unsigned n) v)
    | _ => None
    end.

  Definition storebytes (h : flatmem) (addr : Z) (bytes : list memval) : flatmem :=
    setN bytes addr h.

End FlatMem.

Notation flatmem := FlatMem.flatmem.

Inductive SyncChannel :=
  | SyncChanUndef
  | SyncChanValid (to senderpaddr count busy : int).

Definition SyncChanPool := ZMap.t SyncChannel.

Inductive BigLockEvent :=
  | BWAIT_LOCK (curid : Z) (n : nat)
  | BGET_LOCK (curid : Z)
  | BREL_LOCK (curid : Z) (s : SyncChanPool).

Definition PageBuffer := list int.

Inductive BigSharedMemEvent :=
  | BPALLOCE (curid : Z) (b : Z)
  | BBUFFERE (curid cv_id : Z) (msg : PageBuffer) (* for message passing *)
  | BTDSPAWN (curid : Z) (new_id : Z) (q : Z) (* for general variables *)
             (ofs : int) (* for kernel stack *)
             (buc : block) (ofs_uc : int) (* for user context *)
  | BTDYIELD (curid : Z)
  | BTDSLEEP (slp_id cv_id : Z) (* sleep id = curid *)
             (s : SyncChanPool) (* for message passing *)
  | BTDWAKE (curid : Z) (cv_id : Z)
  | BTDWAKE_DIFF (curid : Z) (cv_id wk_id cpu_id : Z).

Inductive BigOracleEventUnit :=
  | TBLOCK (lock_id : Z) (e : BigLockEvent)
  | TBSHARED (e : BigSharedMemEvent).

Inductive BigOracleEvent :=
  | TBEVENT (i : Z) (e : BigOracleEventUnit).

Definition BigLog := list BigOracleEvent.

Inductive BigLogType :=
  | BigUndef
  | BigDef (l : BigLog).

Definition UContext := ZMap.t val.
Definition UContextPool := ZMap.t UContext.

Parameter LEnv : forall ET : Type, Z -> ET.

Record DeviceData {T : Type} := mkDevData {
  s : T;   (* internal state *)
  l1 : Z;  (* local log 1 *)
  l2 : Z;  (* local log 2 *)
  l3 : Z   (* local log 3 *)
}.
Arguments mkDevData {_}.

Inductive ParityType := pOdd | pEven | pHigh | pLow | pNone.

Record SerialState := mkSerialState {
  Base : Z;
  SerialOn : bool; (* Serial exists *)
  SerialIrq : bool; (* Interrupt is pending *)
  RxIntEnable : bool;
  TxBuf : list Z;
  RxBuf : list Z;
  DLAB : bool;
  Baudrate : Z;
  Databits : Z;
  Stopbits : Z;
  Parity : ParityType;
  Fifo : Z;
  Modem : Z
}.

Inductive SerialEvent :=
  | NullEvent
  | SerialRecv (s : list Z)
  | SerialSendComplete
  | SerialPlugin.

Definition SerialEnv := LEnv SerialEvent.
Definition SerialData := @DeviceData SerialState.

(* Oracle assumptions *)
Axiom SerialRecv_in_range : forall idx str,
  SerialEnv idx = SerialRecv str ->
  Forall (fun c => 0 <= c <= 255) str.

Record SerialDriver := mkSerialDriver {
  serial_exists : Z
}.

Record ConsoleDriver := mkConsoleDriver {
  cons_buf : list (Z * Z * nat); (* console buffer *)
  rpos : Z                       (* reading position *)
}.

Record IoApicState := mkIoApicState {
  IoApicInit : bool;
  CurrentIrq : option (Z * Z);
  IoApicBase : Z;
  IoApicId : Z;
  IoApicMaxIntr : Z;
  IoApicIrqs : list Z;
  IoApicEnables : list bool
}.

Definition IoApicData := @DeviceData IoApicState.

Inductive SyscallEvent :=
  | SyscallGetc (r : Z)
  | SyscallPutc (c : Z).

Inductive IOEvent :=
| IOEvRecv (logIdx : Z) (strIdx : nat) (c : Z)
| IOEvSend (logIdx : Z) (c : Z)
| IOEvGetc (logIdx : Z) (strIdx : nat) (c : Z)
| IOEvPutc (logIdx : Z) (c : Z).

Record RData := mkRData {
  CPU_ID : Z; (* current CPU_ID *)
  pg : bool; (* abstract of CR0, indicates whether the paging is enabled or not *)
  ikern : bool; (* pure logic flag, shows whether it's in kernel mode or not *)
  ihost : bool; (* logic flag, shows whether it's in the host mode or not *)
  HP : flatmem;
  cid : ZMap.t Z; (* current thread id *)
  init : bool; (* pure logic flag, show whether the initialization at this layer has been called or not *)
  big_log : BigLogType;
  uctxt : UContextPool; (* user context pool *)
  com1 : SerialData; (* serial port COM1 *)
  drv_serial : SerialDriver; (* serial driver states *)
  console : ConsoleDriver; (* console driver states *)
  ioapic : IoApicData; (* I/O Advanced Programmable Interrupt Controller *)
  intr_flag : bool;
  in_intr : bool; (* in the interrupt handler *)
  io_log : list IOEvent;
}.

Class ThreadsConfigurationOps := {
  dev_handling_cid : Z; (* specific thread for handling device drivers *)
}.

Definition update_CPU_ID (a : RData) b :=
  let (_, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData b pg ikern ihost HP cid init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log .
Definition update_pg (a : RData) b :=
  let (CPU_ID, _, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID b ikern ihost HP cid init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_ikern (a : RData) b :=
  let (CPU_ID, pg, _, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg b ihost HP cid init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_ihost (a : RData) b :=
  let (CPU_ID, pg, ikern, _, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern b HP cid init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_HP (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, _, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost b cid init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_cid (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, _, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP b init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_init (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, _, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid b big_log uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_big_log (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, _, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init b uctxt com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_uctxt (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, _, com1, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log b com1 drv_serial console ioapic intr_flag in_intr io_log.
Definition update_com1 (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, _, drv_serial, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt b drv_serial console ioapic intr_flag in_intr io_log.
Definition update_drv_serial (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, _, console, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt com1 b console ioapic intr_flag in_intr io_log.
Definition update_console (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, _, ioapic, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt com1 drv_serial b ioapic intr_flag in_intr io_log.
Definition update_ioapic (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, _, intr_flag, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt com1 drv_serial console b intr_flag in_intr io_log.
Definition update_intr_flag (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, _, in_intr, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt com1 drv_serial console ioapic b in_intr io_log.
Definition update_in_intr (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, _, io_log) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt com1 drv_serial console ioapic intr_flag b io_log.
Definition update_io_log (a : RData) b :=
  let (CPU_ID, pg, ikern, ihost, HP, cid, init, big_log, uctxt, com1, drv_serial, console, ioapic, intr_flag, in_intr, _) := a in
  mkRData CPU_ID pg ikern ihost HP cid init big_log uctxt com1 drv_serial console ioapic intr_flag in_intr b.

Notation "a '{' 'CPU_ID' : x }" := (update_CPU_ID a x) (at level 1).
Notation "a '{' 'pg' : x }" := (update_pg a x) (at level 1).
Notation "a '{' 'ikern' : x }" := (update_ikern a x) (at level 1).
Notation "a '{' 'ihost' : x }" := (update_ihost a x) (at level 1).
Notation "a '{' 'HP' : x }" := (update_HP a x) (at level 1).
Notation "a '{' 'cid' : x }" := (update_cid a x) (at level 1).
Notation "a '{' 'init' : x }" := (update_init a x) (at level 1).
Notation "a '{' 'big_log' : x }" := (update_big_log a x) (at level 1).
Notation "a '{' 'uctxt' : x }" := (update_uctxt a x) (at level 1).
Notation "a '{' 'com1' : x }" := (update_com1 a x) (at level 1).
Notation "a '{' 'drv_serial' : x }" := (update_drv_serial a x) (at level 1).
Notation "a '{' 'console' : x }" := (update_console a x) (at level 1).
Notation "a '{' 'ioapic' : x }" := (update_ioapic a x) (at level 1).
Notation "a '{' 'intr_flag' : x }" := (update_intr_flag a x) (at level 1).
Notation "a '{' 'in_intr' : x }" := (update_in_intr a x) (at level 1).
Notation "a '{' 'io_log' : x }" := (update_io_log a x) (at level 1).

Definition update_cons_buf (a : ConsoleDriver) b :=
  let (_, rpos) := a in mkConsoleDriver b rpos.
Definition update_rpos (a : ConsoleDriver) b :=
  let (cons_buf, _) := a in mkConsoleDriver cons_buf b.

Notation "a '{' 'cons_buf' : x }" := (update_cons_buf a x) (at level 1).
Notation "a '{' 'rpos' : x }" := (update_rpos a x) (at level 1).

Notation "a '{' 'console' '/' 'cons_buf' : x }" := (update_console a (update_cons_buf (console a) x)) (at level 1).
Notation "a '{' 'console' '/' 'rpos' : x }" := (update_console a (update_rpos (console a) x)) (at level 1).

Definition update_s {T : Type} (a : @DeviceData T) (b : T) :=
  let (_, l1, l2, l3) := a in mkDevData b l1 l2 l3.
Definition update_l1 {T : Type} (a : @DeviceData T) b :=
  let (s, _, l2, l3) := a in mkDevData s b l2 l3.
Definition update_l2 {T : Type} (a : @DeviceData T) b :=
  let (s, l1, _, l3) := a in mkDevData s l1 b l3.
Definition update_l3 {T : Type} (a : @DeviceData T) b :=
  let (s, l1, l2, _) := a in mkDevData s l1 l2 b.

Notation "a '{' 's' : x }" := (update_s a x) (at level 1).
Notation "a '{' 'l1' : x }" := (update_l1 a x) (at level 1).
Notation "a '{' 'l2' : x }" := (update_l2 a x) (at level 1).
Notation "a '{' 'l3' : x }" := (update_l3 a x) (at level 1).

Definition update_Base (a : SerialState) b :=
  let (_, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState b SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_SerialOn (a : SerialState) b :=
  let (Base, _, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base b SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_SerialIrq (a : SerialState) b :=
  let (Base, SerialOn, _, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn b RxIntEnable TxBuf RxBuf DLAB Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_RxIntEnable (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, _, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq b TxBuf RxBuf DLAB Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_TxBuf (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, _, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable b RxBuf DLAB Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_RxBuf (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, _, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf b DLAB Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_DLAB (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, _, Baudrate, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf b Baudrate Databits Stopbits Parity Fifo Modem.
Definition update_Baudrate (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, _, Databits, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB b Databits Stopbits Parity Fifo Modem.
Definition update_Databits (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, _, Stopbits, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate b Stopbits Parity Fifo Modem.
Definition update_Stopbits (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, _, Parity, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate Databits b Parity Fifo Modem.
Definition update_Parity (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, _, Fifo, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate Databits Stopbits b Fifo Modem.
Definition update_Fifo (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, _, Modem) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate Databits Stopbits Parity b Modem.
Definition update_Modem (a : SerialState) b :=
  let (Base, SerialOn, SerialIrq, RxIntEnable, TxBuf, RxBuf, DLAB, Baudrate, Databits, Stopbits, Parity, Fifo, _) := a in
  mkSerialState Base SerialOn SerialIrq RxIntEnable TxBuf RxBuf DLAB Baudrate Databits Stopbits Parity Fifo b.

Notation "a '{' 'Base' : x }" := (update_Base a x) (at level 1).
Notation "a '{' 'SerialOn' : x }" := (update_SerialOn a x) (at level 1).
Notation "a '{' 'SerialIrq' : x }" := (update_SerialIrq a x) (at level 1).
Notation "a '{' 'RxIntEnable' : x }" := (update_RxIntEnable a x) (at level 1).
Notation "a '{' 'TxBuf' : x }" := (update_TxBuf a x) (at level 1).
Notation "a '{' 'RxBuf' : x }" := (update_RxBuf a x) (at level 1).
Notation "a '{' 'DLAB' : x }" := (update_DLAB a x) (at level 1).
Notation "a '{' 'Baudrate' : x }" := (update_Baudrate a x) (at level 1).
Notation "a '{' 'Databits' : x }" := (update_Databits a x) (at level 1).
Notation "a '{' 'Stopbits' : x }" := (update_Stopbits a x) (at level 1).
Notation "a '{' 'Parity' : x }" := (update_Parity a x) (at level 1).
Notation "a '{' 'Fifo' : x }" := (update_Fifo a x) (at level 1).
Notation "a '{' 'Modem' : x }" := (update_Modem a x) (at level 1).

Notation "a '{' 'com1' '/' 's' : x }" := (update_com1 a (update_s (com1 a) x)) (at level 1).
Notation "a '{' 'com1' '/' 'l1' : x }" := (update_com1 a (update_l1 (com1 a) x)) (at level 1).
Notation "a '{' 'com1' '/' 'l2' : x }" := (update_com1 a (update_l2 (com1 a) x)) (at level 1).
Notation "a '{' 'com1' '/' 'l3' : x }" := (update_com1 a (update_l3 (com1 a) x)) (at level 1).

Notation "a '{' 'com1' '/' 's' '/' 'Base' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Base (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'SerialOn' : x }" :=
  (update_com1 a (update_s (com1 a) (update_SerialOn (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'SerialIrq' : x }" :=
  (update_com1 a (update_s (com1 a) (update_SerialIrq (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'RxIntEnable' : x }" :=
  (update_com1 a (update_s (com1 a) (update_RxIntEnable (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'TxBuf' : x }" :=
  (update_com1 a (update_s (com1 a) (update_TxBuf (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'RxBuf' : x }" :=
  (update_com1 a (update_s (com1 a) (update_RxBuf (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'DLAB' : x }" :=
  (update_com1 a (update_s (com1 a) (update_DLAB (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'Baudrate' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Baudrate (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'Databits' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Databits (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'Stopbits' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Stopbits (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'Parity' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Parity (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'Fifo' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Fifo (s (com1 a)) x))) (at level 1).
Notation "a '{' 'com1' '/' 's' '/' 'Modem' : x }" :=
  (update_com1 a (update_s (com1 a) (update_Modem (s (com1 a)) x))) (at level 1).

Definition update_IoApicInit (a : IoApicState) b :=
  let (_, CurrentIrq, IoApicBase, IoApicId, IoApicMaxIntr, IoApicIrqs, IoApicEnables) := a in
  mkIoApicState b CurrentIrq IoApicBase IoApicId IoApicMaxIntr IoApicIrqs IoApicEnables.
Definition update_CurrentIrq (a : IoApicState) b :=
  let (IoApicInit, _, IoApicBase, IoApicId, IoApicMaxIntr, IoApicIrqs, IoApicEnables) := a in
  mkIoApicState IoApicInit b IoApicBase IoApicId IoApicMaxIntr IoApicIrqs IoApicEnables.
Definition update_IoApicBase (a : IoApicState) b :=
  let (IoApicInit, CurrentIrq, _, IoApicId, IoApicMaxIntr, IoApicIrqs, IoApicEnables) := a in
  mkIoApicState IoApicInit CurrentIrq b IoApicId IoApicMaxIntr IoApicIrqs IoApicEnables.
Definition update_IoApicId (a : IoApicState) b :=
  let (IoApicInit, CurrentIrq, IoApicBase, _, IoApicMaxIntr, IoApicIrqs, IoApicEnables) := a in
  mkIoApicState IoApicInit CurrentIrq IoApicBase b IoApicMaxIntr IoApicIrqs IoApicEnables.
Definition update_IoApicMaxIntr (a : IoApicState) b :=
  let (IoApicInit, CurrentIrq, IoApicBase, IoApicId, _, IoApicIrqs, IoApicEnables) := a in
  mkIoApicState IoApicInit CurrentIrq IoApicBase IoApicId b IoApicIrqs IoApicEnables.
Definition update_IoApicIrqs (a : IoApicState) b :=
  let (IoApicInit, CurrentIrq, IoApicBase, IoApicId, IoApicMaxIntr, _, IoApicEnables) := a in
  mkIoApicState IoApicInit CurrentIrq IoApicBase IoApicId IoApicMaxIntr b IoApicEnables.
Definition update_IoApicEnables (a : IoApicState) b :=
  let (IoApicInit, CurrentIrq, IoApicBase, IoApicId, IoApicMaxIntr, IoApicIrqs, _) := a in
  mkIoApicState IoApicInit CurrentIrq IoApicBase IoApicId IoApicMaxIntr IoApicIrqs b.

Notation "a '{' 'ioapic' '/' 's' : x }" := (update_ioapic a (update_s (ioapic a) x)) (at level 1).

Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicInit' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicInit (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'CurrentIrq' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_CurrentIrq (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicBase' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicBase (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicId' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicId (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicMaxIntr' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicMaxIntr (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicIrqs' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicIrqs (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicIrqs' '[' n ']' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicIrqs (s (ioapic a))
                                                           (replace x n (IoApicIrqs (s (ioapic a))))))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicEnables' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicEnables (s (ioapic a)) x))) (at level 1).
Notation "a '{' 'ioapic' '/' 's' '/' 'IoApicEnables' '[' n ']' : x }" :=
  (update_ioapic a (update_s (ioapic a) (update_IoApicEnables (s (ioapic a))
                                                              (replace x n (IoApicEnables (s (ioapic a))))))) (at level 1).

(** Constants *)
Notation TOTAL_CPU := 8.
Notation CONS_BUFFER_SIZE := 512.
Notation CONS_BUFFER_MAX_CHARS := (CONS_BUFFER_SIZE - 1).
Notation SERIAL_HW_BUF_SIZE := 12%nat.
Notation INTR_ENABLE_REC_MAX := 100%nat.
Notation INTR_DISABLE_REC_MAX := 100%nat.
Notation U_ESI := 1.
Notation U_EBX := 4.
Notation U_EAX := 7.
Notation CHAR_CR := 13.
Notation CHAR_LF := 10.
Notation NEXT_SEND_MAX_REC := (Z.to_nat 12800).
Notation E_SUCC := 0.
Notation E_NOCHAR := 1.
Notation E_SENDFAIL := 2.

Section Specs.
Context `{ThreadsConfigurationOps}.

Definition mkRecvEvents (logIdx : Z) (cs : list Z) : list IOEvent :=
  map (fun ic : nat * Z => let (i, c) := ic in IOEvRecv logIdx i c) (enumerate cs).

(** Interrupts *)
Definition cons_intr_aux (abd : RData) : option RData :=
  match (abd.(ikern), abd.(ihost), abd.(init), abd.(in_intr)) with
  | (true, true, true, true) =>
    if zeq 1 abd.(drv_serial).(serial_exists) then
      match abd.(com1) with
      | mkDevData (mkSerialState _ true true true nil rxbuf false _ _ _ _ _ _) lrx _ _ =>
        match SerialEnv (lrx - 1) with
        | SerialRecv str =>
          if list_eq_dec zeq str rxbuf then
            let rxbuf' := map (fun ic : nat * Z => let (i, c) := ic in (c, lrx - 1, i)) (enumerate rxbuf) in
            if zle (Zlength (abd.(console).(cons_buf) ++ rxbuf')) CONS_BUFFER_MAX_CHARS
            then Some abd {console / cons_buf : abd.(console).(cons_buf) ++ rxbuf'}
                          {com1 / l1 : lrx + Zlength rxbuf' * 2 + 1}
                          {com1 / s / RxBuf : nil}
                          {com1 / s / SerialIrq : false}
                          {io_log : abd.(io_log) ++ mkRecvEvents (lrx - 1) str}
            else Some abd {console / cons_buf :
                            skipn (Z.to_nat (Zlength (abd.(console).(cons_buf) ++ rxbuf') - CONS_BUFFER_MAX_CHARS))
                                  (abd.(console).(cons_buf) ++ rxbuf')}
                          {console / rpos : (abd.(console).(rpos) + Zlength (abd.(console).(cons_buf) ++ rxbuf') + 1) mod CONS_BUFFER_SIZE}
                          {com1 / l1 : lrx + Zlength rxbuf' * 2 + 1}
                          {com1 / s /RxBuf : nil}
                          {com1 / s /SerialIrq : false}
                          {io_log : abd.(io_log) ++ mkRecvEvents (lrx - 1) str}
          else None
        | _ => None
        end
      | _ => None
      end
    else None
  | _ => None
  end.

Fixpoint serial_intr_enable_aux (n : nat) (abd : RData) : option RData :=
  match n with
  | O => Some abd
  | S n' =>
    if abd.(com1).(s).(SerialIrq) then
      match cons_intr_aux abd with
      | Some d1 => serial_intr_enable_aux n' d1
      | None => None
      end
    else Some abd
  end.

Definition serial_trans_env_rx (e : SerialEvent) (s : SerialState) : SerialState :=
  let (_, _, _, rxint, _, rxbuf, _, _, _, _, _, _, _) := s in
  match e with
  | SerialPlugin => s {SerialOn : true}
  | SerialRecv str =>
    let s' := s {RxBuf : skipn (length (rxbuf ++ str) - SERIAL_HW_BUF_SIZE) (rxbuf ++ str)} in
    if rxint then s' {SerialIrq : true} else s'
  | _ => s
  end.

Definition serial_trans_env_tx (e : SerialEvent) (s : SerialState) : SerialState * option Z :=
  match e with
  | SerialSendComplete => (s {TxBuf : nil}, hd_error s.(TxBuf))
  | _ => (s, None)
  end.

Definition serial_intr (d : SerialData) : SerialData * list IOEvent :=
  let s' := serial_trans_env_rx (SerialEnv d.(l1)) d.(s) in
  let (s'', c) := serial_trans_env_tx (SerialEnv d.(l2)) s' in
  (* TODO: fake logIdx for now until figure out how to relate to Putc events *)
  let new := match c with Some c' => IOEvSend 0 c' :: nil | _ => nil end in
  (d {s : s''} {l1 : d.(l1) + 1} {l2 : d.(l2) + 1}, new).

Fixpoint serial_intr_disable_aux (n : nat) (masked : bool) (abd : RData) : option RData :=
  match n with
  | O => Some abd
  | S n' =>
    let (data, new) := serial_intr abd.(com1) in
    let d0 := abd {com1 : data} {io_log : abd.(io_log) ++ new}in
    if d0.(com1).(s).(SerialIrq) then
      if masked then serial_intr_disable_aux n' true d0
      else match cons_intr_aux d0 with
           | Some d1 => serial_intr_disable_aux n' false d1
           | None => None
           end
    else Some abd
  end.

Definition serial_intr_enable_spec (abd : RData) : option RData :=
  match (abd.(ikern), abd.(ihost), abd.(init), abd.(intr_flag), abd.(in_intr)) with
  | (true, true, true, true, false) =>
    match nth_error abd.(ioapic).(s).(IoApicIrqs) 4 with
    | Some v =>
      match nth_error abd.(ioapic).(s).(IoApicEnables) 4 with
      | Some true =>
        match serial_intr_enable_aux INTR_ENABLE_REC_MAX (abd {in_intr : true}) with
        | Some d => Some (d {in_intr : false} {ioapic / s / IoApicEnables [(Z.to_nat 4)] : true})
        | None => None
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end.

Definition serial_intr_disable_spec (abd : RData) : option RData :=
  match (abd.(ikern), abd.(ihost), abd.(init), abd.(intr_flag), abd.(in_intr)) with
    | (true, true, true, true, false) =>
      let masked :=
          match nth_error abd.(ioapic).(s).(IoApicIrqs) 4 with
          | Some v =>
            match nth_error abd.(ioapic).(s).(IoApicEnables) 4 with
            | Some true =>
              if abd.(intr_flag) then false
              else true (* iflag of CPU is cleared *)
            | _ => true (* interrupt line has been maksed *)
            end
          | None => true (* interrupt is not configured *)
          end
      in match serial_intr_disable_aux INTR_DISABLE_REC_MAX masked (abd {in_intr : true}) with
      | Some d => Some (d {in_intr : false} {ioapic / s / IoApicEnables [(Z.to_nat 4)] : false})
      | None => None
      end
    | _ => None
  end.

Definition thread_serial_intr_enable_spec (abd : RData) : option RData :=
  if zeq (ZMap.get abd.(CPU_ID) abd.(cid)) dev_handling_cid
  then if abd.(init) then serial_intr_enable_spec abd else None else None.

Definition thread_serial_intr_disable_spec (abd : RData) : option RData :=
  if zeq (ZMap.get (abd.(CPU_ID)) (abd.(cid))) dev_handling_cid
  then if abd.(init) then serial_intr_disable_spec abd else None else None.

(** User context *)
Fixpoint B_GetContainerUsed_aux (tid : Z) (cid : Z) (l : BigLog) : bool :=
  match l with
  | nil => false
  | TBEVENT cpuid e :: l' =>
    match e with
    | TBSHARED (BTDSPAWN _ new_id _ _ _ _) =>
      if zeq cid cpuid then
        if zeq tid new_id then true else B_GetContainerUsed_aux tid cid l'
      else B_GetContainerUsed_aux tid cid l'
    | _ => B_GetContainerUsed_aux tid cid l'
    end
  end.

Definition B_GetContainerUsed (tid : Z) (cid : Z) (l : BigLog) : bool :=
  if zeq tid (cid + 1) then true
  else if zle_le 0 tid TOTAL_CPU then false
  else B_GetContainerUsed_aux tid cid l.

Definition uctx_arg2_spec (adt : RData) : option Z :=
  let cpu := adt.(CPU_ID) in
  let curid := ZMap.get adt.(CPU_ID) adt.(cid) in
  match (adt.(init), adt.(ikern), adt.(pg), adt.(ihost)) with
  | (true, true, true, true) =>
    match adt.(big_log) with
    | BigDef l =>
      if B_GetContainerUsed curid cpu l then
        match (ZMap.get U_EBX (ZMap.get curid adt.(uctxt))) with
        | Vint n => Some (Int.unsigned n)
        | _ => None
        end
      else None
    | _ => None
    end
  | _ => None
  end.

Definition uctx_arg3_spec (adt : RData) : option Z :=
  let cpu := adt.(CPU_ID) in
  let curid := ZMap.get adt.(CPU_ID) adt.(cid) in
  match (adt.(init), adt.(ikern), adt.(pg), adt.(ihost)) with
  | (true, true, true, true) =>
    match adt.(big_log) with
    | BigDef l =>
      if B_GetContainerUsed curid cpu l then
        match (ZMap.get U_ESI (ZMap.get curid adt.(uctxt))) with
        | Vint n => Some (Int.unsigned n)
        | _ => None
        end
      else None
    | _ => None
    end
  | _ => None
  end.

Definition uctx_set_retval1_spec (n : Z) (adt : RData) : option RData :=
  let cpu := adt.(CPU_ID) in
  let curid := ZMap.get adt.(CPU_ID) adt.(cid) in
  match (adt.(init), adt.(ikern), adt.(pg), adt.(ihost)) with
  | (true, true, true, true) =>
    match adt.(big_log) with
    | BigDef l =>
      if B_GetContainerUsed curid cpu l then
        let uctx := ZMap.get curid adt.(uctxt) in
        let uctx' := ZMap.set U_EBX (Vint (Int.repr n)) uctx in
        Some adt {uctxt : ZMap.set curid uctx' adt.(uctxt)}
      else None
    | _ => None
    end
  | _ => None
  end.

Definition uctx_set_errno_spec (n : Z) (adt : RData) : option RData :=
  let cpu := adt.(CPU_ID) in
  let curid := ZMap.get adt.(CPU_ID) adt.(cid) in
  match (adt.(init), adt.(ikern), adt.(pg), adt.(ihost)) with
  | (true, true, true, true) =>
    match adt.(big_log) with
    | BigDef l =>
      if B_GetContainerUsed curid cpu l then
        let uctx := ZMap.get curid adt.(uctxt) in
        let uctx' := ZMap.set U_EAX (Vint (Int.repr n)) uctx in
        Some adt {uctxt : ZMap.set curid uctx' adt.(uctxt)}
      else None
    | _ => None
    end
  | _ => None
  end.

(** Serial Driver *)
Fixpoint putc_scan_log (t : Z) (bound : nat) : option Z :=
  match bound with
  | O => None
  | S bound' =>
    match SerialEnv t with
    | SerialSendComplete => Some t
    | _ => putc_scan_log (t + 1) bound'
    end
  end.

Definition next_sendcomplete (t : Z) :=
  match putc_scan_log t NEXT_SEND_MAX_REC with
  | None => None
  | Some i => Some (i + 1)
  end.

Definition serial_putc_spec (c : Z) (abd : RData) : option (RData * Z) :=
  let c' := c mod 256 in
  match (abd.(ikern), abd.(init), abd.(ihost)) with
  | (true, true, true) =>
    if zeq 1 abd.(drv_serial).(serial_exists) then
      match abd.(com1) with
      | mkDevData (mkSerialState _ true _ _ txbuf nil false _ _ _ _ _ _) _ ltx _ =>
        let cs := if zeq c' CHAR_LF then CHAR_LF :: CHAR_CR :: nil else c' :: nil in
        match txbuf with
        | nil => Some (abd {com1 / s / TxBuf : cs} {com1 / l2 : ltx + 1}
                           {io_log : abd.(io_log) ++ IOEvPutc ltx c :: nil}, c')
        | _ =>
          match next_sendcomplete ltx with
          | Some ltx' => Some (abd {com1 / s / TxBuf : cs} {com1 / l2 : ltx'}
                                   {io_log : abd.(io_log) ++ IOEvPutc ltx c :: nil}, c')
          | None => None
          end
        end
      | _ => None
      end
    else Some (abd, -1)
  | _ => None
  end.

(** Console *)
Definition cons_buf_read_spec (abd : RData) : option (RData * Z) :=
  match (abd.(ikern), abd.(ihost), abd.(init)) with
  | (true, true, true) =>
    let s := abd.(console) in
    let b := s.(cons_buf) in
    let r := s.(rpos) in
    match b with
    | nil => Some (abd, -1)
    | (c, logIdx, strIdx) :: tl =>
      Some (abd {console : s {cons_buf : tl}
                             {rpos : (r + 1) mod CONS_BUFFER_SIZE}}
                {io_log : abd.(io_log) ++ IOEvGetc logIdx strIdx c :: nil}, c)
    end
  | _ => None
  end.

Fixpoint cons_buf_read_loop_spec (n : nat) (read : nat) (addr : Z) (abd : RData) : option (RData * Z) :=
  match n with
  | O => Some (abd, Z.of_nat read)
  | S n' =>
    match cons_buf_read_spec abd with
    | Some (abd', c) =>
      if zeq c (-1) then Some (abd, Z.of_nat read)
      else
        let m' := FlatMem.store Mint8unsigned abd.(HP) addr (Vint (Int.repr c)) in
        cons_buf_read_loop_spec n' (S read) addr (abd' {HP : m'})
    | None => None
    end
  end.

Definition thread_cons_buf_read_spec (abd : RData) : option (RData * Z) :=
  if zeq (ZMap.get abd.(CPU_ID) abd.(cid)) dev_handling_cid
  then if abd.(init) then cons_buf_read_spec abd else None else None.

Definition thread_serial_putc_spec (c : Z) (abd : RData) : option (RData * Z) :=
  if zeq (ZMap.get abd.(CPU_ID) abd.(cid)) dev_handling_cid
  then if abd.(init) then serial_putc_spec c abd else None else None.

Definition thread_cons_buf_read_loop_spec (len addr : Z) (abd : RData) : option (RData * Z) :=
  if zeq (ZMap.get abd.(CPU_ID) abd.(cid)) dev_handling_cid
  then if abd.(init) then cons_buf_read_loop_spec (Z.to_nat len) O addr abd else None else None.

(** Syscalls *)
Definition sys_getc_spec (abd : RData) : option RData :=
  match thread_serial_intr_disable_spec abd with
  | Some d1 =>
    match thread_cons_buf_read_spec d1 with
    | Some (d2, x) =>
      match thread_serial_intr_enable_spec d2 with
      | Some d3 =>
        match uctx_set_retval1_spec x d3 with
        | Some d4 =>
          let err := if zeq x (-1) then E_NOCHAR else E_SUCC in
          uctx_set_errno_spec err d4
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Definition sys_putc_spec (abd : RData) : option RData :=
  match uctx_arg2_spec abd with
  | Some c =>
    match thread_serial_intr_disable_spec abd with
    | Some d1 =>
      match thread_serial_putc_spec c d1 with
      | Some (d2, x) =>
        match thread_serial_intr_enable_spec d2 with
        | Some d3 =>
          match uctx_set_retval1_spec x d3 with
          | Some d4 =>
            let err := if zeq x (-1) then E_SENDFAIL else E_SUCC in
            uctx_set_errno_spec err d4
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Definition sys_getcs_spec (abd : RData) : option RData :=
  match uctx_arg2_spec abd, uctx_arg3_spec abd with
  | Some buf_vaddr, Some len =>
    match thread_serial_intr_disable_spec abd with
    | Some d1 =>
      match thread_cons_buf_read_loop_spec len buf_vaddr d1 with
      | Some (d2, read) =>
        match thread_serial_intr_enable_spec d2 with
        | Some d3 =>
          match uctx_set_retval1_spec read d3 with
          | Some d4 =>
            uctx_set_errno_spec E_SUCC d4
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | _, _ => None
  end.

End Specs.
