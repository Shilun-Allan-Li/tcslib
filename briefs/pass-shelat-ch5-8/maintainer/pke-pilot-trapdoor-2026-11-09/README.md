# Trapdoor bit encryption and the Goldreich–Levin bridge

Seyoon merged the [oracle security move #259](https://github.com/Shilun-Allan-Li/tcslib/pull/259) at `b1743e78750bdb9e93f0d3f5b95af60b2f7fa9fa`.
[PR #260](https://github.com/Shilun-Allan-Li/tcslib/pull/260) implements the next slice of the
[approved PKE pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md)
at `31401c7192d0e0fab716805527c1e232f82736d4`.

`Trapdoor` owns the predicate evaluator, Algorithm 104.3, its correctness
and security proof, and the two Goldreich–Levin bridge theorems. The bridge
keeps the encoding-width premise. `TrapdoorPredictor` owns the reduction
machine, its coin split and its prediction identity. Both legacy imports
re-export their original interfaces. The padded CPA corollary belongs to
the oracle adapter and uses the pending `SingleBitSecure.padded_cpa` bridge.

- All 12 affected modules pass, including the library root and campaign
  Checks. The replay verifies 1,071 retained objects. The Checks object
  and output match the pinned #259 baseline.
- The new and both legacy imports pass standalone probes, including a
  check of the existing `tdpPredictor_coins` simp rule. The new construction
  imports the ensemble interface independently of the oracle games.
- The census matches all 182 declarations. It maps 74 to new homes and
  accounts for 6 private names and compiler-generated binder labels.
  Type and definition terms, reference sets, and axiom dependencies match.
- The 5 whole-file seals apply 7,824 requests. The focused
  Checks seal passes. The explicit tactic and generated-equation scans
  find zero scoped reads. The thirteen sensitivity controls transfer
  through identical checked closures, and the equation collector reruns
  both its controls.
- Plain style lint reports zero findings. Campaign lint retains the two
  inherited reader warnings for `pkPredictor` and `predCoins`.

| Current file | Inherited diagnostics |
|---|---:|
| `Trapdoor.lean` | 3 |
| `TrapdoorPredictor.lean` | 2 |

`READS.json` maps the 5 inherited source steps and preserves the 10
earlier ensemble rows. `VERIFICATION.json` pins the checked evidence.
`trapdoor-checks.zip` has SHA-256 `67765e8062682bce6eb9a4fc2dbbd480fe9f17295e8a340befced0d5a12684c1`.

**Clear to merge — the trapdoor relocation and compatibility imports pass.**
