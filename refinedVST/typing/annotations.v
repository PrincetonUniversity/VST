From VST.typing Require Import base.

Inductive to_uninit_annot : Type :=
  ToUninit.

Inductive stop_annot : Type :=
  StopAnnot.

Inductive share_annot : Type :=
  ShareAnnot.

Inductive unfold_once_annot : Type :=
  UnfoldOnceAnnot.

Inductive learn_annot : Type :=
  LearnAnnot.

Inductive learn_alignment_annot : Type :=
  LearnAlignmentAnnot.

Inductive LockAnnot : Type := LockA | UnlockA.

Inductive reduce_annot : Type :=
  ReduceAnnot.

Inductive assert_annot : Type :=
  AssertAnnot (s : string).
