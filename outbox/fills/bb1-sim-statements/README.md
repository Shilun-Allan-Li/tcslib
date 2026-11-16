# Claude statement job `bb1-sim-statements` (the bb1-sim statement phase and its reader probe)

Claude is the worker, a lead with up to 1 sub-agent (standing ruling: Claude for fills and all other external jobs).
The job writes the statement phase that Seyoon ruled on 2026-11-16 (`../rulings.md`, Q1–Q11, on `../design-r1.md`)
for the pairing fill unit `bb1-sim` (T2 `bb1_sim_real`, T3 `bb1_sim_random`). Three deliverables:
1. `stmt/games-relational`: the new `Games/Relational.lean` (`ProbComp.expect_simulate_rel`, the target, `sorry`;
   `prob_simulate_rel`, proved from it; `expect_sample_rel`, `sorry`), the public averaging bound
   `ProbComp.abs_expect_sub_le_expect` in `Games/Probability.lean` (Q6, proved), and the `Games` facade's import and
   `## Contents` line. Its own small PR on the records tip (Q9).
2. `stmt/pairing-group-helpers`: the Q10 helpers (`Z_p ≃ G` for `g ≠ 1` as a bijectivity lemma, the additive and
   negation exponent laws in `G`, injectivity of natural casts below the order), proved, as pure insertions into the
   frozen `Pairing/Group.lean`, unless Mathlib already states them.
3. The reader probe (not for landing): on T4's delivered head, the minimal readers T2 needs in `Defs.lean` and
   `BonehBoyen.lean` (starting from `IBEScheme.sidImpl_eq_oracleImpl`, Q7, and an `encCT` reader only if needed),
   proved in a probe module, with a consumer probe proving T2's step M from them under the development seals A and B.
   It reports the exact text to insert, for Seyoon's advance scope ruling. No `Defs.lean` or `BonehBoyen.lean` edit
   is on any branch.

T2 and T3 stay `sorry`; their fill is a later job, stacked on T4's PR. Q8's bb1-sim gate (after Gate 44) audits this
statement phase together with the reader insertions and the fill.

**Base.** `bdcadd858cbe043e8c41e465a96e81feb1eecda1`, the records tip at issue (fetched by name): the DW-8 ingest
commit, which carries the [BGZ09] and [Sho04] ingests and the review's citation strings, so the job cites them
directly (Q11). No `.lean` file changed from `9d0122e408e2962e3f7c06f1c66e13a2b8725eb4` to the base; the IBE and
`Games` files are #331's (`9e7a96481785d6cac4dea3b2e990c49ac278b060`). **Probe base**
`c90273fad3511ada7c9c1a53e1abdd8478237cee`, T4's final head, reproduced by `git am` of the delivery's patches (exchange
`inbox/fills/bb1-machine/`, final commit `f14ac810da888829d21a1bd94fef4dcd4258b863`) onto
`7c0a55e0239c14786612d0cd4462e64238543ca1`, the pushed tip of `fill/pairings-bb1-machine`.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1 with an adaptation for this
job: two bases, one package tree, two olean trees). Verify the package with `shasum -a 256 -c SHA256SUMS` from this
directory. The design note, the rulings, the ingests and the review are at the base; the brief lists their SHA-256s.

- [Build order](order.txt): 612 TCSlib modules at the base, in import order (a subsequence of the depth-first
  post-order of the 1,351 modules reachable from `TCSlib.lean`). They are the upstream closure of every module
  downstream of `Games/Probability.lean` or `Pairing/Group.lean`, with the root `TCSlib` excluded, as in every fill of
  this campaign; the maintainer builds the root at landing. `Games/Probability` is module 257, `Games/Simulate` 320
  (insert the new `Games/Relational` after it), the facade `Games` 428, `Pairing/Group` 593.
- [Closures](closures.txt): the sets behind the order, with each module's position in the full import order:
  `UP-STMT` (4, the upstream of the new module's imports), `DOWN-PROBABILITY` (151 with the root: the series 1 sweep
  is its 150 non-root modules, `EncryptThenTag/Forgery` and the facade among them), `DOWN-GROUP` (12 with the root:
  the series 2 sweep is its 11) and `BUILD-GROUP` (110, the bootstrap prefix for series 2).
- [Mathlib roots](roots.txt): 124, the Mathlib modules the 612 modules import directly. T4's 94 roots (the probe's
  tree) are a subset.
- [Source hashes](SOURCE-SHA256SUMS) of the 612 files at the base, read from the git objects.
- [Base admissions](base-sorries.txt): 28 declarations in 14 modules, from a syntactic scan (comments and strings
  stripped, `sorry` tokens attributed to the enclosing declaration); among them T1, T2, T3 and T4 (T4 is proved only
  on its PR). Series 1 must add exactly `expect_simulate_rel` and `expect_sample_rel` (30 in 15); series 2 adds none.
- The probe's tree uses T4's delivered `evidence/build/order-final.txt` (189 modules, on the exchange).

**Size** (maintainer's assessment). About 160–200 lines in `Relational.lean`, about 15 in `Probability.lean`, 4 in
the facade, 40–70 in `Group.lean`, and a probe of about 300–600 lines outside the library. The long steps are the
612-module bootstrap, the 150-module sweep downstream of `Probability.lean` and the probe's 189-module tree, one Lean
process at a time. One job is right; the suggested split gives the probe to the sub-agent in its own worktree and
olean tree. Checkpoint 1 is the probe, because it feeds Seyoon's scope ruling (Q7).

Claude returns at least one checkpoint and the final only at `inbox/fills/bb1-sim-statements/` on the exchange; it
never pushes a campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md` (beside this file in
`briefs/pairings/fills/bb1-sim/issued-stmt-r1/`; it is not part of the pack).

**Maintainer steps before dispatch:** commit this folder to the records, write that commit's full hash for
`<RECORDS-PIN>` in `dispatch.md`, and push the exchange commit named there. If it is replayed onto a newer exchange
tip, its hash changes: put the pushed hash in `dispatch.md` (and its parent) before dispatching.

**Ready to dispatch**
