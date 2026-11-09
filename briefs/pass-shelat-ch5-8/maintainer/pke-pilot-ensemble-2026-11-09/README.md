# Public-key ensemble security and hybrid relocation

Seyoon merged the [scheme interfaces #257](https://github.com/Shilun-Allan-Li/tcslib/pull/257) at `e9f470f828db562e04e2243122b24b29a9bab581`.
[PR #258](https://github.com/Shilun-Allan-Li/tcslib/pull/258) implements the next slice of the
[approved pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md)
at `313a0a9de4818417172e693512dc7a98943eaef1`.

`EnsembleSecurity.lean` owns the single-bit, single-message and fixed-vector
experiments and the two security proofs. `Hybrid.lean` owns the shared-key
bound and imports the polynomial-time reduction from `HybridMachine.lean`.
The facade lists all three leaves. `Asymptotic/PublicKey.lean` and
`Asymptotic/PublicKeyLemmas.lean` continue to expose their original interfaces.
They retain the trapdoor construction and its predictor. The one additional
lemma, `BitPublicKeyScheme.pkEncDist_eq`, supplies the sampler equation to
the trapdoor ciphertext proof.

- The replay compiles all 13 affected modules and verifies 1,067
  retained objects. The library root passes. The campaign Checks object
  and output match the checked #257 inputs. All three standalone import probes pass.
- The native census compares 400 existing declarations and the new equation.
  It records 90 rehomed identities and 6 private names whose module
  scope changed. The type and definition comparisons preserve binder flags
  and normalize the generated labels and private names. All existing axiom
  dependencies match. The new equation has the same axiom dependencies as
  the sampler. The only changed proof references are the equation and its
  pair projections in the trapdoor ciphertext proof.
- 8 whole-file seals and 4 focused probes check the moved
  definitions and downstream imports. The original thirteen sensitivity
  controls transfer through identical source and object closures. The fresh
  generated-equation collector passes both of its controls. The explicit
  tactic scan and generated-equation collector find zero scoped reads.
- Plain style lint has zero findings. Campaign lint reports zero failures
  and retains the inherited equation-reader warnings. The old public-key
  file falls from 1,023 to 570 lines.

The 15 inherited diagnostics match the original source steps and declaration
identities. Their current homes feed the final seal cleanup.

| Current file | Inherited diagnostics |
|---|---:|
| `EnsembleSecurity.lean` | 6 |
| `Hybrid.lean` | 3 |
| `HybridMachine.lean` | 1 |
| `PublicKey.lean` | 3 |
| `PublicKeyLemmas.lean` | 2 |

`READS.json` maps their ledger IDs, declaration homes, ranges and provider
evidence. `VERIFICATION.json` pins the comparison and archive.
`ensemble-checks.zip` has SHA-256 `ebbf9e7cc54d595d9ca28de40cd64155ba698a0af3dee8ae3f9eb2be2f8c2acb`.

**Clear to merge — the relocation and both compatibility paths pass.**
