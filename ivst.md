# Building VST-on-Iris (VST 3.x)

## Option 1: Use OPAM

VST-on-Iris releases are now available on OPAM as part of the `coq-released` repo, and can be installed automatically -- look for versions numbered 3.x. It may take a few months for new versions to appear on OPAM.

## Option 2: Build from Source

You can either clone the current master branch, or download a release from the [Releases](https://github.com/PrincetonUniversity/VST/releases) page. Each release lists the major Iris version and CompCert version it has been tested with (CompCert is only necessary if you want to `clightgen` your own C files), and master will usually work with the same versions as the latest release. The code may also work with dev Iris versions, but probably not those any earlier than the listed version. You will also need to install `coq-flocq`, probably via OPAM.

Once the dependencies are installed and you have the code, run `make -j` to build VST. If you clone the repo, you may first need to do `git submodule update --init ora` to initialize the ORA submodule.

## Running Examples

Run `make *.vo` to compile any example proof. For instance, to compile the [proof for the list reverse function](./progs64/verif_reverse2.v):

```(bash)
make progs64/verif_reverse2.vo -j
```

To generate a `_CoqProject` file for external use:

```(bash)
make _CoqProject
```

## For legacy VST users: `VST` and `VST_on_Iris` name conversion

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
