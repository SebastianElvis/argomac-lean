# argomac-lean

The ArgoMAC garbled circuit for BN254 scalar multiplication, in Lean 4.

This repository is the baseline submission for the Kriterion challenge
`scalar-multiplication`.

## Layout

| Path                                 | Content                                   |
| ------------------------------------ | ----------------------------------------- |
| `Construction.lean`, `Construction/` | The computable construction.              |
| `Proof.lean`, `Proof/`               | The proof.                                |
| `Submission.lean`                    | The entry point the verifier reads.       |
| `tests/`                             | Acceptance checks. Kriterion ignores them. |

The verifier copies `Submission.lean`, `Construction.lean`, `Proof.lean`,
`Construction/`, and `Proof/` into a workspace it generates. It ignores every other
root entry.

## Build

The construction and the proof import the challenge library. That library is
`examples/bn254-scalar-multiplication/formal` in the Kriterion repository, and
`challenge.yaml` pins its commit. To build this repository, place that library beside
these files and declare it as the Lean library `Kriterion`. Kriterion does this for
every submission it verifies.

## Source

The paper source is
<https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116>.
