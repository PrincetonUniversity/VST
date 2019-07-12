(** printing \2/ $\cup$ #&cup;# *)
(** printing <2= $\subseteq$ #&sube;# *)
(** printing forall $\forall$ #&forall;# *)
(** printing -> $\rightarrow$ #&rarr;# *)
(** printing /\ $\land$ #&and;# *)

Require Import Setoid Program.
Require Import VST.concurrency.paco.src.paco.



(** * Illustrating the [paco] library

    This tutorial shows how to use our [paco] library to reason about
    coinductive predicates in Coq.  By coinductive predicates we mean
    objects that one can define using [CoInductive] and whose type
    ends in [Prop].  The library implements _parameterized
    coinduction_, as described in our draft paper entitled #<a
    href=" http://plv.mpi-sws.org/paco/"># _The Power of
    Parameterization in Coinductive Proof_ #</a>#.

    How does parameterized coinduction compare to Coq's existing
    support for coinductive proofs?

    For proofs by _induction_, Coq provides a tactic called [fix], but
    proofs done directly with [fix] are required to satisfy a
    _syntactic guardedness_ criterion.  Fortunately, Coq also
    generates induction _lemmas_ for every inductive definition, which
    eliminate the need to ever use the low-level [fix] tactic and
    worry about guardedness.  For proofs by coinduction, Coq provides
    a tactic [cofix] analogous to [fix], i.e., also based on a
    syntactic guardedness criterion.  However, Coq does not generate
    any lemmas for coinductive definitions.  Consequently, to reason
    about such definitions, the user must use the low-level [cofix]
    tactic.  Due to its syntactic nature, [cofix] is problematic in
    several ways (please see the paper linked above for detailed
    discussion of these points):

    - It is non-compositional.
    - It is inefficient.
    - It is not user-friendly.
    - It interacts poorly with builtin automation tactics.


    The [paco] library provides a tactic, [pcofix], which can be seen
    as a replacement for Coq's builtin [cofix] tactic (in the case of
    predicates) that does not involve any syntactic guardedness
    criterion and thus avoids all of these problems.  In addition,
    like Coq's [cofix], [pcofix] provides built-in support for
    _incremental_ proofs, i.e., proofs in which the coinduction
    hypothesis is extended gradually as the proof progresses.

    We believe this combination of compositionality, incrementality,
    robustness, and ease of use makes [pcofix] a superior alternative
    to [cofix] for proofs about coinductive predicates.

    The rest of this tutorial illustrates the use of the [paco]
    library with the help of three examples.
*)(* *)



(** ** Example: stream equality

    The first example involves streams of natural numbers and an
    equality thereon.  We prove a particular equality via [cofix], and
    then explain how that proof can be turned into one via [pcofix].
*)


(** We start by defining a type of streams of natural numbers.
*)

CoInductive stream :=
  | cons : nat -> stream -> stream.


(** The following, seemingly useless, lemma is a common trick for
    working with corecursive terms such as our streams.  (It will be
    used in the example proofs.)  For details, see for instance #<a
    href="http://adam.chlipala.net/cpdt/html/Coinductive.html">Adam
    Chlipala's book on Certified Programming with Dependent
    Types</a>#.
*)

Definition sunf s :=
  match s with cons n s' => cons n s' end.

Lemma sunf_eq : forall s, s = sunf s.
Proof.
  destruct s; auto.
Qed.


(** In order to state our example equality, we define an enumeration
    stream and a map operation for streams.
*)

CoFixpoint enumerate n : stream :=
  cons n (enumerate (S n)).

CoFixpoint map f s : stream :=
  match s with cons n s' => cons (f n) (map f s') end.



(** *** A proof using [cofix]

    We will now prove, using [cofix], that for any [n] the stream
    [enumerate n] is equal to the stream [cons n (map S (enumerate n))].
*)


(** First, we define an equality [seq] on streams.  Usually, one would
    do this as follows.

    [CoInductive seq : stream -> stream -> Prop :=] #<br>#
    [  | seq_fold : forall n s1 s2 (R : seq s1 s2), seq (cons n s1) (cons n s2).]

    Instead, we define the generating function, [seq_gen], beforehand,
    and then define [seq] as its greatest fixed point using
    [CoInductive].  The reason is simply that we need [seq_gen] later
    when using [paco].  If applying parameterized coinduction to an
    existing development where the generating function is not
    explicit, it can always easily be made explicit.

    Note that, albeit the use of [Inductive], the definition
    of [seq_gen] is not recursive.
*)

Inductive seq_gen seq : stream -> stream -> Prop :=
  | _seq_gen : forall n s1 s2 (R : seq s1 s2 : Prop), seq_gen seq (cons n s1) (cons n s2).
Hint Constructors seq_gen.



CoInductive seq : stream -> stream -> Prop :=
  | seq_fold : forall s1 s2, seq_gen seq s1 s2 -> seq s1 s2.


(** Second, we do the actual proof.
*)

Theorem example : forall n, seq (enumerate n) (cons n (map S (enumerate n))).
Proof.
  cofix CIH.
  intros; apply seq_fold.
  pattern (enumerate n) at 1; rewrite sunf_eq; simpl.
  constructor.
  rewrite (sunf_eq (enumerate n)); simpl.
  rewrite (sunf_eq (map _ _)); simpl.
  apply CIH.
Qed.

(** _Note_: One might want to eliminate the use of [pattern] in the
    proof script by replacing the corresponding line with the
    following:

    [rewrite sunf_eq at 1; simpl.]

    However, doing so will result in an invalid proof (rejected at
    [Qed]-time).  The reason is that the proof term created by
    [rewrite] ... [at 1] involves some lemmas from the [Setoid]
    library.  Like most lemmas, these are opaque, so guardedness
    checking cannot inspect their proofs and thus fails.  This is a
    great example of two of the previously mentioned problems with the
    [cofix] approach, namely lack of compositionality and poor
    interaction with standard tactics.
*)(* *)



(** *** A proof using our [pcofix]

    We will now do the same proof, but using the [paco] library.  We
    first simply show the new (but equivalent) definition of stream
    equality and the new proof of the example, and then explain what
    is going on behind the scenes.  In both, we use [paco] constructs
    with suffix "2" because we are dealing with predicates of arity 2
    here.

    _Note_: [Paco] supports predicates of arity up to 8.  Also, it
    supports up to three mutually coinductive predicates (see the last
    example of this tutorial).  In either case, extending this is just
    a matter of copy and paste.

    We also have to prove monotonicity of the generating function
    [seq_gen], which can be discharged by the tactic [pmonauto], and
    register it in the Hint databse [paco].

    _Remark_: Unlike [CoInductive], [paco] does not care whether the
    generating function is given in a _strictly positive_ syntactic
    form; all that matters is that the function is monotone. More
    specifically, [paco2 f] is well defined for an arbitrary generating
    function [f] regardless of whether it is monotone or not. However,
    in order to ensure that [paco2 f bot2] is the greatest fixed point
    of [f], we need monotonicity of [f].
*)

Definition seq' s1 s2 := paco2 seq_gen bot2 s1 s2.
Hint Unfold seq'.
Lemma seq_gen_mon: monotone2 seq_gen. Proof. pmonauto. Qed.
Hint Resolve seq_gen_mon : paco.

Theorem example' : forall n, seq' (enumerate n) (cons n (map S (enumerate n))).
Proof.
  pcofix CIH.
  intros; pfold.
  rewrite sunf_eq at 1; simpl.
  constructor.
  rewrite (sunf_eq (enumerate n)); simpl.
  rewrite (sunf_eq (map _ _)); simpl.
  right; apply CIH.
Qed.

(** Observe that the proof script is essentially the same as before
    (this is no accident).  The main change is the use of [pcofix]
    instead of [cofix], which allows us to avoid any syntactic
    guardedness checking at [Qed]-time.  As a minor benefit of that,
    we are able to use [rewrite] ... [at 1], which we could not do
    before.  *)



(** **** How it works:

    To understand [seq'] and the proof of [example'], we have to
    explain some background.  Given a monotone function [f], we call
    [paco2 f] the _parameterized_ greatest fixed point of [f].  For a
    relation [r], [paco2 f r] is defined as the greatest fixed point
    of the function [fun x => f (x \2/ r)].  Clearly, [paco2 f bot2]
    (where [bot2] is the empty relation) is just the ordinary greatest
    fixed point of [f].

    Let us look at our example domain to understand better.  A proof
    of [paco2 seq_gen r s1 s2] can be seen as a proof of [r <2= seq ->
    seq s1 s2], where the use of the premise is guarded
    _semantically_, rather than syntactically.  More precisely, [paco2
    seq_gen r] relates two streams iff their heads are equal and their
    tails are either related by [r] or again related by [paco2 seq_gen
    r].  Compare this to [seq], the ordinary greatest fixed point of
    [seq_gen], which relates two streams iff their heads are equal and
    their tails are again related by [seq].  This should also make it
    clear why our definition of [seq'] is equivalent to [seq].

    To fold and unfold parameterized fixed points, we provide two
    tactics, where [upaco2 f r := paco2 f r \2/ r]:

    - [pfold] : when the conclusion is [paco2 f r] for some [f] and
      [r], [pfold] converts it to [f (upaco2 f r)]
    - [punfold H] : when the hypothesis [H] is [paco2 f r] for some
      [f] and [r], [punfold H] converts it to [f (upaco2 f r)]

    Other useful lemmas are:

    - [paco2_mon f : monotone2 (paco2 f)]
    - [paco2_mult f : forall r, paco2 f (paco2 f r) <2= paco2 f r]
    - [paco2_mult_strong f : forall r, paco2 f (upaco2 f r) <2= paco2 f r]


    We will see an example involving [paco2_mult] in a moment.  But
    first let us have another look at the proof scripts of [example]
    and [example'].  In the former, after calling [cofix], the proof
    state is as follows:

    [CIH : forall n : nat, seq (enumerate n) (cons n (map S (enumerate n)))] #<br>#
    [============================] #<br>#
    [forall n : nat, seq (enumerate n) (cons n (map S (enumerate n)))] #<br>#

    In this state, the hypothesis precisely matches the conclusion,
    and there is nothing preventing one from simply concluding the
    goal directly.  Of course, if one were to do that, one's "proof"
    would be subsequently rejected by [Qed] for failing to obey
    syntactic guardedness.

    Calling [pcofix] results in a similar state, except that the added
    hypothesis [CIH] now governs a fresh relation variable [r], which
    represents the current coinduction hypothesis relating [enumerate n]
    and [cons n (map S (enumerate n))] for all [n].  The new goal
    then says that, in proving the two streams equal, we can use [r]
    coinductively, but only in a semantically guarded position,
    i.e. after unfolding [paco2 seq_gen r].  In particular, one
    _cannot_ apply [CIH] immediately to "solve" the goal:

    [r : stream -> stream -> Prop] #<br>#
    [CIH : forall n : nat, r (enumerate n) (cons n (map S (enumerate n)))] #<br>#
    [============================] #<br>#
    [forall n : nat, paco2 seq_gen r (enumerate n) (cons n (map S (enumerate n)))] #<br>#

    The remaining differences between the proof scripts of [example]
    and [example'] are as follows.  First, let us examine [example].
    After applying [seq_fold] and unfolding [enumerate n] in the proof
    of [example], we have the following goal:

    [CIH : forall n : nat, seq (enumerate n) (cons n (map S (enumerate n)))] #<br>#
    [n : nat] #<br>#
    [============================] #<br>#
    [seq_gen seq (cons n (enumerate (S n))) (cons n (map S (enumerate n)))] #<br>#

    By the definition of [seq_gen] and unfolding [map S (enumerate n)],
    this reduces to showing

    [CIH : forall n : nat, seq (enumerate n) (cons n (map S (enumerate n)))] #<br>#
    [n : nat] #<br>#
    [============================] #<br>#
    [seq (enumerate (S n)) (cons (S n) (map S (enumerate (S n))))] #<br>#

    which follows directly by applying the coinduction hypothesis [CIH].

    In the case of [example'], the proof is slightly different.
    First, we use the tactic [pfold] rather than [apply seq_fold],
    simply because we now reason about [seq'] rather than [seq].
    After applying [pfold] and unfolding [enumerate n], we have:

    [r : stream -> stream -> Prop] #<br>#
    [CIH : forall n : nat, r (enumerate n) (cons n (map S (enumerate n)))] #<br>#
    [n : nat] #<br>#
    [============================] #<br>#
    [seq_gen (paco2 seq_gen r \2/ r) (cons n (enumerate (S n))) (cons n (map S (enumerate n)))] #<br>#

    As you see, the relation [r] appears in the argument of
    [seq_gen]. Thus by definition of [seq_gen] and unfolding [map S
    (enumerate n)], we need to show [enumerate (S n)] and [cons (S n)
    (map S (enumerate (S n)))] are related by either [paco2 seq_gen r]
    or [r]:

    [r : stream -> stream -> Prop] #<br>#
    [CIH : forall n : nat, r (enumerate n) (cons n (map S (enumerate n)))] #<br>#
    [n : nat] #<br>#
    [============================] #<br>#
    [paco2 seq_gen r (enumerate (S n)) (cons (S n) (map S (enumerate (S n))))] #<br>#
    [ \/ r (enumerate (S n)) (cons (S n) (map S (enumerate (S n))))] #<br>#

    As the coinduction hypothesis gives us that they are related by [r],
    we first have to select the [right] disjunct, before we apply
    [CIH].

    Summing up, the two proofs are very similar, but in the one using
    [paco], the guardedness of the coinduction is guaranteed at every
    step by the way the proof is constructed, rather than by a
    syntactic check of the whole proof term after the fact.
 *)(* *)



(** *** Another example

    Before moving on to the second part, we briefly demonstrate the
    use of the tactics [punfold] and [pclearbot].
*)(* *)


(** Here is a proof for [seq].
*)

Theorem seq_cons : forall n1 n2 s1 s2 (SEQ : seq (cons n1 s1) (cons n2 s2)),
  n1 = n2 /\ seq s1 s2.
Proof.
  intros.
  inversion_clear SEQ; rename H into SEQ.
  inversion_clear SEQ; auto.
Qed.


(** And here is the corresponding proof for [seq'].

  Note that the tactic [pclearbot] simplifies all hypotheses of the form [upaco{n} gf bot{n}] to [paco{n} gf bot{n}].
*)

Theorem seq'_cons : forall n1 n2 s1 s2 (SEQ : seq' (cons n1 s1) (cons n2 s2)),
  n1 = n2 /\ seq' s1 s2.
Proof.
  intros.
  punfold SEQ.
  inversion_clear SEQ; pclearbot; auto.
Qed.

(** We also provide two tactics [pdestruct] and [pinversion].
    They are simply defined as follows:

    - [pdestruct H] := [punfold H; destruct H; pclearbot]
    - [pinversion H] := [punfold H; inversion H; pclearbot]

    Using this the proof of the above theorem [seq'_cons] can be
    simplified as [intros; pinversion SEQ; auto.]
*)(* *)



(** ** Example: infinite tree equality

    The second example involves infinite binary trees of natural
    numbers and an equality thereon.  We prove two particular
    equalities via [cofix] in an incremental fashion, and then show
    how these proofs can be done just as easily via [pcofix].
    We then show how, using [pcofix], the proofs can additionally
    be modularly decomposed.

*)


(** As before, we first define the coinductive type and the unfolding
    trick.
*)

CoInductive inftree :=
  | node : nat -> inftree -> inftree -> inftree.

Definition tunf t : inftree :=
  match t with node n tl tr => node n tl tr end.

Lemma tunf_eq : forall t, t = tunf t.
Proof.
  destruct t; auto.
Qed.


(** In order to state our example equalities, we define the following
    four trees.
*)

CoFixpoint one : inftree := node 1 one two
with       two : inftree := node 2 one two.

CoFixpoint eins : inftree := node 1 eins (node 2 eins zwei)
with       zwei : inftree := node 2 eins zwei.



(** *** Incremental proofs using [cofix]

    As before, we define the tree equality as the greatest fixed point
    of its generating function.
*)

Inductive teq_gen teq : inftree -> inftree -> Prop :=
  | _teq_gen : forall n t1l t1r t2l t2r (Rl : teq t1l t2l : Prop) (Rr : teq t1r t2r),
                 teq_gen teq (node n t1l t1r) (node n t2l t2r).
Hint Constructors teq_gen.

CoInductive teq t1 t2 : Prop :=
  | teq_fold (IN : teq_gen teq t1 t2).


(** We now prove, using [cofix], that [one] equals [eins] and,
    separately, that [two] equals [zwei].  Note the nested use of
    [cofix] in either proof script, which lets us strengthen the
    coinductive hypothesis in the middle of the proof.  For instance,
    in the proof [teq_one], we start out with the coinductive
    hypothesis that [one] and [eins] are equal ([CIH]).  Later on, we
    use [cofix] again to additionally assume that [two] and [zwei] are
    equal ([CIH']).  This is a prime example of _incremental_ proof:
    we start with no coinductive assumptions, and we progressively add
    more coinductive assumptions as the proof progresses.
*)

Theorem teq_one : teq one eins.
Proof.
  cofix CIH.
  apply teq_fold.
  rewrite (tunf_eq one), (tunf_eq eins); simpl.
  constructor; auto.
  apply teq_fold.
  rewrite (tunf_eq two); simpl.
  constructor; auto.
  cofix CIH'.
  apply teq_fold.
  rewrite (tunf_eq two), (tunf_eq zwei); simpl.
  constructor; auto.
Qed.

Theorem teq_two : teq two zwei.
Proof.
  cofix CIH.
  apply teq_fold.
  rewrite (tunf_eq two), (tunf_eq zwei); simpl.
  constructor; auto.
  cofix CIH'.
  apply teq_fold.
  rewrite (tunf_eq one), (tunf_eq eins); simpl.
  constructor; auto.
  apply teq_fold.
  rewrite (tunf_eq two); simpl.
  constructor; auto.
Qed.



(** *** Incremental proofs using our [pcofix]

    As before, we can easily turn the above [cofix]-proofs into
    [pcofix]-proofs.
*)

Definition teq' t1 t2 := paco2 teq_gen bot2 t1 t2.
Hint Unfold teq'.
Lemma teq_gen_mon: monotone2 teq_gen. Proof. pmonauto. Qed.
Hint Resolve teq_gen_mon : paco.

Theorem teq'_one : teq' one eins.
Proof.
  pcofix CIH.
  pfold.
  rewrite (tunf_eq one), (tunf_eq eins); simpl.
  constructor; auto.
  left; pfold.
  rewrite (tunf_eq two); simpl.
  constructor; auto.
  left; pcofix CIH'.
  pfold.
  rewrite (tunf_eq two), (tunf_eq zwei); simpl.
  constructor; auto.
Qed.

Theorem teq'_two : teq' two zwei.
Proof.
  pcofix CIH.
  pfold.
  rewrite (tunf_eq two), (tunf_eq zwei); simpl.
  constructor; auto.
  left; pcofix CIH'.
  pfold.
  rewrite (tunf_eq one), (tunf_eq eins); simpl.
  constructor; auto.
  left; pfold.
  rewrite (tunf_eq two); simpl.
  constructor; auto.
Qed.



(** *** Pseudo-compositional proofs using [cofix]

    It is easy to see that the proofs of [teq_one] and [teq_two] are
    essentially the same.  We can avoid duplicating some work by
    decomposing the proofs as follows.

    First we prove that [teq two zwei] holds under the coinductive
    assumption [teq one eins].  This is basically the second part of
    the proof of [teq_one] (and the first part of the proof of
    [teq_two]).  Then we prove the converse, i.e., that [teq one
    eins] holds under the coinductive assumption [teq two zwei].
    This is basically the first part of the proof of [teq_one] (and
    the second part of the proof of [teq_two]).

    The issue is that there seems to be no way to express these two
    properties.  The best we can do is prove [teq two zwei -> teq one
    eins] and [teq one eins -> teq two zwei], and make sure that in
    these proofs any use of the assumption is syntactically guarded.
    For instance, we are not allowed to prove [teq two zwei -> teq
    one eins] by inspecting [teq two zwei] and extracting [teq one
    eins] from that (see the proof of [teq_two_one_bad] below).
    Although a valid proof of that goal by itself, it could not be
    composed later to yield a proof of [teq one eins] or [teq two
    zwei] (see the aborted theorem [teq_eins_bad] below).

    Moreover, both lemmas must then be made transparent by using
    [Defined] instead of [Qed] at the end, such that, when composing
    them to prove [teq one eins] or [teq two zwei], guardedness
    checking can inspect their proof terms.  In other words, [cofix]
    is not properly compositional.
*)

Lemma teq_two_one_bad : teq two zwei -> teq one eins.
Proof.
  intros; rewrite (tunf_eq two), (tunf_eq zwei) in H.
  destruct H; inversion IN; auto.
Defined.

Lemma teq_two_one : teq two zwei -> teq one eins.
Proof.
  intros; cofix CIH.
  apply teq_fold.
  rewrite (tunf_eq one), (tunf_eq eins); simpl.
  constructor; auto.
  apply teq_fold.
  rewrite (tunf_eq two); simpl.
  constructor; auto.
Defined.

Lemma teq_one_two : teq one eins -> teq two zwei.
Proof.
  intros; cofix CIH.
  apply teq_fold.
  rewrite (tunf_eq two), (tunf_eq zwei); simpl.
  constructor; auto.
Defined.

Theorem teq_eins : teq one eins.
Proof.
  cofix CIH.
  apply teq_two_one, teq_one_two, CIH.
Qed.

Theorem teq_zwei : teq two zwei.
Proof.
  cofix CIH.
  apply teq_one_two, teq_two_one, CIH.
Qed.


(** The following proof would fail guardedness checking at [Qed]-time,
    because in the proof of the lemma [teq_two_one_bad] the
    assumption is used "too early".
*)

Theorem teq_eins_bad : teq one eins.
Proof.
  cofix CIH.
  apply teq_two_one_bad, teq_one_two, CIH.
Abort.



(** *** Compositional proofs using our [pcofix]

    Using parameterized coinduction, we can state the actual desired
    lemmas as follows and prove them using [pcofix] (again, only
    minimal changes to the previous proof scripts are required).
    Observe that (i) the earlier "wrong" proof of [teq two zwei -> teq
    one eins] ([teq_two_one_bad]) is _not_ a proof of the
    corresponding lemma here, and (ii) we are not forced to make the
    lemmas transparent.
*)

Lemma teq'_two_one : forall r,
  (r two zwei : Prop) -> paco2 teq_gen r one eins.
Proof.
  intros; pcofix CIH.
  pfold.
  rewrite (tunf_eq one), (tunf_eq eins); simpl.
  constructor; auto.
  left; pfold.
  rewrite (tunf_eq two); simpl.
  constructor; auto.
Qed.

Lemma teq'_one_two : forall r,
  (r one eins : Prop) -> paco2 teq_gen r two zwei.
Proof.
  intros; pcofix CIH.
  pfold.
  rewrite (tunf_eq two), (tunf_eq zwei); simpl.
  constructor; auto.
Qed.


(** We now compose them with the help of the lemma [paco2_mult]:
    - [paco2_mult f : paco2 f (paco2 f r) <2= paco2 f r]

    The tactic [pmult] applies [paco{n}_mult] to the conclusion
    for an appropriate [n].
*)

Theorem teq'_eins : teq' one eins.
Proof.
  pcofix CIH.
  pmult; apply teq'_two_one, teq'_one_two, CIH.
Qed.

Theorem teq'_zwei : teq' two zwei.
Proof.
  pcofix CIH.
  pmult; apply teq'_one_two, teq'_two_one, CIH.
Qed.



(** ** Example: mutual coinduction

    The third and last example shows that [paco] also works for mutual
    coinduction.  Here, the mutuality involves two predicates.
*)(* *)


(** We define two generating functions (using the [inftree] type from
    before).
*)

Inductive eqone_gen eqone eqtwo : inftree -> Prop :=
  | _eqone_gen : forall tl tr (EQL : eqone tl : Prop) (EQR : eqtwo tr : Prop),
                    eqone_gen eqone eqtwo (node 1 tl tr).

Inductive eqtwo_gen eqone eqtwo : inftree -> Prop :=
  | _eqtwo_gen : forall tl tr (EQL : eqone tl : Prop) (EQR : eqtwo tr : Prop),
                   eqtwo_gen eqone eqtwo (node 2 tl tr).

Hint Constructors eqone_gen eqtwo_gen.



(** *** A proof via [cofix]

    Using these, we now define two mutually coinductive predicates
    [eqone] and [eqtwo].  It is easy to see intuitively that they
    contain all trees that are equal to [one] and [two] from above,
    respectively.  We then prove that [eqone] contains [eins].
*)

CoInductive eqone (t : inftree) : Prop :=
  | eqone_fold (EQ : eqone_gen eqone eqtwo t)
with eqtwo (t : inftree) : Prop :=
  | eqtwo_fold (EQ : eqtwo_gen eqone eqtwo t).

Lemma eqone_eins : eqone eins.
Proof.
  cofix CIH0; apply eqone_fold.
  rewrite tunf_eq; simpl; constructor.
    apply CIH0.
  cofix CIH1; apply eqtwo_fold.
  constructor.
    apply CIH0.
  rewrite tunf_eq; apply CIH1.
Qed.



(** *** A proof via [pcofix]

    To define the [paco] versions of [eqone] and [eqtwo], we apply
    the two constructors [paco1_2_0] and [paco1_2_1], respectively ("1"
    because we are dealing with unary predicates).  Again, the
    translation of the lemma and of its proof is almost trivial.
*)

Definition eqone' t := paco1_2_0 eqone_gen eqtwo_gen bot1 bot1 t.
Definition eqtwo' t := paco1_2_1 eqone_gen eqtwo_gen bot1 bot1 t.
Hint Unfold eqone' eqtwo'.
Lemma eqone_gen_mon: monotone1_2 eqone_gen. Proof. pmonauto. Qed.
Lemma eqtwo_gen_mon: monotone1_2 eqtwo_gen. Proof. pmonauto. Qed.
Hint Resolve eqone_gen_mon eqtwo_gen_mon : paco.

Lemma eqone'_eins: eqone' eins.
Proof.
  pcofix CIH0; pfold.
  rewrite tunf_eq; simpl; constructor.
    right; apply CIH0.
  left; pcofix CIH1; pfold.
  constructor.
    right; apply CIH0.
  right; rewrite tunf_eq; apply CIH1.
Qed.

(** _Remark_: For three mutually coinductive predicates, the
    constructors are [paco{n}_3_0], [paco{n}_3_1], and [paco{n}_3_2].
*)




(*Proving the safety thing*)

Section safety.
  Context (X:Type)
  (P: X -> X -> Prop).

  CoInductive path x: Prop:=
  | step x': path x' -> P x x' -> path x.

  CoInductive stutter_path x: nat -> Prop :=
  | step' n1 n2 x':  stutter_path x' n1 -> P x x' -> stutter_path x n2
  | stutter n : stutter_path x n -> stutter_path x (S n).

  Inductive path_gen path : X -> Prop :=
  | _path_gen : forall x x', P x x' -> path x' -> path_gen path x.

  Definition path' := paco1 path_gen.

  Inductive stutterpath_gen (stutterpath : X -> nat -> Prop) : X -> nat -> Prop:=
  | _stutterpath_step : forall n1 n2 x x', P x x' -> stutterpath x' n1 -> stutterpath_gen stutterpath x n2
  | _stutterpath_stut : forall n x, stutterpath x n -> stutterpath_gen stutterpath x (S n).

  Definition stutterpath' := paco2 stutterpath_gen.

  Theorem theorem :
    forall x n,
      stutterpath' bot2 x n ->
      path' bot1  x.
  Proof.
    pcofix CIH. intros x n; revert x; induction n; intros x.
    - intros HH.
      inversion HH. clear HH.
      inversion SIM; subst. clear SIM.
      pfold.
      apply _path_gen with (x' := x'). auto.
      unfold upaco1 in *.
      right.
      apply CIH with n1.
      specialize (LE x' n1 ltac:(assumption)).
      destruct LE. 2: compute in *; tauto.
      unfold stutterpath' in *.
      auto. Guarded.
    - intros HH.
      inversion HH. clear HH.
      inversion SIM; subst; clear SIM.
      + pfold.
        apply _path_gen with (x' := x'). auto.
        unfold upaco1 in *.
        right.
        apply CIH with n1.
        specialize (LE x' n1 ltac:(assumption)).
        destruct LE. 2: compute in *; tauto.
        unfold stutterpath' in *.
        auto. Guarded.
      + pfold.


        Fail continue this.
  Abort.
End safety.
