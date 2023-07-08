# Notes on Fixing `VST_on_Iris`

## Installing ora

```(bash)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -k path coq-iris-ora ./ora
opam install coq-iris-ora
```

## For now we use a very specific version of Iris

Iris pinned to: 8f1ed633426beb3ace044b4515ed54c158cefd23

## `VST` and `VST_on_Iris` name conversion
| VST                       | vst_on_iris                         | syntax                                      |
| ------------------------- | ---------------------------- | ------------------------------------------- |
| prop_right                | bi.pure_intro                | φ → _ -∗ ⌜φ⌝                                |
| andp                      | bi.and                       | ∧                                           |
| andp_right                | bi.and_intro                 | (P -∗ Q) → (P -∗ R) → P -∗ Q ∧ R            |
| andp_left1                | bi.and_elim_l                | P ∧ _ -∗ P                                  |
| andp_left2                | bi.and_elim_r                | _ ∧ Q -∗ Q                                  |
| andp_assoc                | bi.and_assoc                 | && left assoc, ∧ right assoc                |
| andp_comm                 | bi.and_comm                  |                                             |
| andp_derives              | bi.and_mono                  |                                             |
|                           | >                            | ▷                                           |  |
| now_later                 | bi.later_intro               | P -∗ ▷ P                                    |
| intro rho (environ_index) | raise_rho                    |                                             |
| EX                        | ∃                            | becomes Prop                                |
| exp_andp2                 | bi.and_exist_l               | P ∧ (∃ a, Ψ a) ⊣⊢ (∃ a, P ∧ Ψ a)            |
| exp_andp1                 | bi.and_exist_r               | (∃ a, Φ a) ∧ P ⊣⊢ (∃ a, Φ a ∧ P)            |
| exp_left                  | bi.exist_elim                | (∀ a : A, (Φ a -∗ Q)) → (∃ a : A, Φ a) -∗ Q |
| exp_right                 | bi.exist_intro'              | (P -∗ Ψ a) → P -∗ ∃ a0, Ψ a0                |
|                           | semax (E:coPset) Delta P c Q |                                             |
| FF_left                   | bi.False_elim                | False -∗ _                                  |
| \| --                     | ⊢                            |                                             |

also change `apply andp_left1/2` to `rewrite bi.and_elim_l/r`.

derives_trans is a bit different from bi.wand_trans. Can be obtained by:

```(Coq)
Lemma derives_trans: forall {prop:bi} (P Q R:prop),
  (P -∗ Q) -> (Q -∗ R) -> (P -∗ R).
Proof. intros. rewrite H H0 //. Qed.
```

TODO: maybe move this to some library