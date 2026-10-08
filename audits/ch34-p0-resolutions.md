# Chapters 3-4, phase P0 (reception) — audit loop resolutions

**Gate: CLOSED (round 2, 2026-10-08).** Two rounds; the closing round reported
**0 blockers, 0 majors, 3 minors**, all three swept in the closing commit and
re-verified below. The received surface — Hydroxyi's `TimeHierarchy/`,
`SpaceComplexity/`, the `CounterProg` substrate and the five `ClassNP`
additions, 44 modules — is adopted as the chapters-3/4 foundation.

## Round 1 (`audits/ch34-p0-pack.md` → `audits/ch34-p0-findings.md`)

0 blockers, **1 major**, 7 minors, 2 notes; gate held open.

* **Finding 1 (major) — the zero-bound collapse.** Every machine satisfies
  `k ≤ spaceUsed` (each work tape visits its origin), so one zero of `s`
  forces a `SPACE s` decider to zero work tapes globally:
  `SPACE s = SPACE (fun _ => 0)` whenever `s` has a zero; literal
  `SPACE (fun n => n)` is not linear space. Maintainer-verified before repair.
  **Repair**: positive-bound convention adopted (plan §2.4; Ex 3.2 restated at
  `SPACE(n+1)`); collapse documented at the definition site
  (`SpaceComplexity/Basic.lean`); sanity layer
  `SpaceComplexity/ZeroSpace.lean` added (S1-S6). Round 2: **closed**, with
  every sanity statement independently derived true as stated.
* **Findings 2-5, 8 (minors)** — docstring repairs in `CounterProgRun` (plus
  the requested S9 statement `sim_run_of_regs_le`), `Program`, `ARM`,
  `PClosure`, `ARMSim`/`Compile`/`Layout`. Round 2: **closed**.
* **Finding 6 (minor)** — `ReachesB` endpoint wording: repaired, but the
  repair's `Reaches.toB` reference was itself inaccurate; residual swept in
  the closing commit (below).
* **Finding 7 (minor)** — sweep-log provenance: replaced by a sweep recording
  its revision at start. Round 2: **closed** for the replacement evidence;
  the original log's trailing-revision reading stands as a **round-1 pack
  erratum** (acknowledged; shipped packs are never edited).
* **Notes 9-10** — delivered-strength reading of the time hierarchy; the
  non-delivery of general Lemma 4.17. Frozen, no change, both carried into
  the chapters-3/4 statements as recorded in the plan.

## Round 2 (`audits/ch34-p0-r2-pack.md` → `audits/ch34-p0-r2-findings.md`)

**PASS — 0 blockers, 0 majors, 3 minors**, with the repair diff reconstructed
hash-exactly against the round-1 bundle and all ten new statements (S1-S6, S9)
independently derived. Bonus result recorded for fill time: S9's hypotheses
support the tighter bound `t·(2B + 3)`; the stated `t·(2B + 5)` is sound and
deliberately conservative — fills may sharpen it, statement unchanged.

**Closing-commit sweeps (this commit), re-verified:**

| R2 finding | Sweep |
|---|---|
| 6 (residual) | `ReachesB`'s consumer note now states the required separate endpoint hypothesis and says explicitly that `Reaches.toB` does **not** supply it; `Reaches.toB`'s own docstring rewritten (pre-final coordinate → pre-final interval; no reached-configuration bound implied) |
| 11 | "machine-checked" wording corrected to "elaborated sanity statements, proofs deferred to fill" in `ZeroSpace.lean`'s docstring and the plan's §2.4 paragraph |
| 12 | The two timed witness statements added to `ZeroSpace.lean` (sorried, as authorized): `exists_zeroTape_const_oneStep` (zero tapes, `[true]` within one step) and `exists_zeroTape_parity_decider` (zero tapes, `DecidesInTime evenLang (n + 1)`), per the report's own constructions; membership corollaries kept |

Re-verification: `ParseCmp` and `ZeroSpace` re-elaborate with zero errors
(`ZeroSpace` now 11 admission warnings — the nine round-1 statements plus the
two finding-12 witnesses); style lint 0 FAIL over the `SpaceComplexity` tree.

**Round-2 pack erratum (acknowledged):** the pack's phrase "as the log header
records" overstated the sweep-log header — it records the revision, branch,
start time and the wipe statement, but working-tree cleanliness and the
untracked directories were maintainer attestations, not log contents.

## Standing obligations out of this gate

1. **Fill obligations**: the 11 `ZeroSpace` statements and
   `CounterProg.sim_run_of_regs_le` (optionally at the tighter `2B + 3`).
   Scheduled with the chapters-3/4 fill epochs.
2. **The positive-bound convention** binds every future asymptotic space
   statement (`n + 1`, `n^c + 1`, `logSpace`; never a bound with a zero) —
   plan §2.4; the space-hierarchy and Savitch phases must restate it in their
   packs.
3. **Delivered-strength discipline** (notes 9-10): the `f²` time hierarchy is
   never cited as [AB09, Thm 3.1] verbatim until the Hennie-Stearns build
   lands; nothing received is cited as general Lemma 4.17.
4. The P3.1 and P4.1 statement gates, deferred behind this one, are now
   unblocked.
