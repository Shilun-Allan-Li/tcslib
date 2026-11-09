# Reusable safe-prime DDH experiments

Seyoon merged the [trapdoor relocation #260](https://github.com/Shilun-Allan-Li/tcslib/pull/260) at `1db060a35c028f61afb4b9013d29bfd12e7e46b5`.
[PR #261](https://github.com/Shilun-Allan-Li/tcslib/pull/261) starts the ElGamal slice of the
[approved PKE pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md)
at `482e2342b05103f602e9216f89c55427b89e3c42`.

`Candidates.DDH` owns the safe-prime group facts, exponent sampler,
and real and random experiments. The construction continues to import
this module through its original path. The 6 reader equations let the
reduction transport seeds and read samples without unfolding the
experiments. The source check binds the verbatim move and isolates the
changes to 5 private proofs. The existing `eval_ddhLen` simp rule moves
with its definition.

- All 6 affected modules compile, including the library root and
  campaign Checks. The replay verifies 1,078 retained objects.
  Checks output and object bytes match the verified #260 baseline.
- The standalone DDH and ElGamal probes pass. The census checks all
  220 existing declarations and records 40 moved declarations.
  The comparison accounts for 8 generated private names and
  the casts in three private theorem types. Public types, definitions,
  and axiom dependencies match.
- The two whole-file seals pass with 3,024 requests. The focused
  Checks seal passes with the relocated DDH definitions sealed. The
  thirteen sensitivity controls transfer through identical closures,
  and the generated-equation collector reruns its two controls.
- Campaign lint reports zero failures. The old construction file drops
  from 2,134 to 1,835 lines.
  This review keeps the construction and reduction's private arithmetic
  support together. The construction move is a separate review.

The source scan reproduces the 4 inherited core reads in the original
ElGamal module. The following rows give their current positions.

| Ledger ID | Baseline line | Current line |
|---|---:|---:|
| C1-0285 | 1176 | 859 |
| C1-0286 | 1470 | 1153 |
| C1-0287 | 1606 | 1289 |
| C1-0288 | 1680 | 1363 |

`VERIFICATION.json` pins the review. `ddh-checks.zip` contains the
source, probe receipts and ledger. Its SHA-256 is `99d6bece251c8cadaa6c7b2a5de7523c0f84e7c6fc6e3efe13792e9665f0c5e2`.

**Clear to merge — the DDH move and the published-reader boundary pass.**
