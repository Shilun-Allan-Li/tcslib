# Gate 160 round 2 · RAM readers (PR #370)

**Round 2.** Seyoon dispatches and merges. PR #370 is a draft into `complexity/ram-simulation`.

- **Lean head:** `25040f435bba85ad563d5c1f1ceb42744aefc3eb` (branch `ram/readers`).
- **Round 1** audited `e75d2907` and returned HOLD (0 blockers, 1 major, 1 minor; `findings.md`,
  verbatim). This round checks the resolutions in `resolutions.md`.
- `pack.md` is round 1's. This round's evidence is in `evidence-r2/`.

## What changed since round 1

1. **G160-02:** the docstrings of `WordRAM.simTime_eq`, `simSpace_eq` and
   `Turing.FinNDTM.decidesInSpace_iff` now state their formulas and clauses (`7ee903a4`).
2. **Four readers for the vendored run calculus** (Seyoon, 2026-11-17). They are added to
   `Programs/WordRAM/Steps.lean`, [AFM26]'s vendored file, and listed as TCSlib additions in its
   header's local-modifications list:
   - `WordRAM.step_def`: `step P c` as its `match` on the instruction at `c.pc`;
   - `WordRAM.effect_def`: `effect i m` as its `match`;
   - `WordRAM.Steps.zero_iff` and `WordRAM.Steps.succ_iff`: the two cases of `Steps`.

   Each restates its definition and is `rfl` or `Iff.rfl`. The vendored definitions and lemmas
   are unchanged. Tier 0 (`fill-ram-steps`, the 18 admissions of `Programs/WordRAM/Extended`,
   added to the scope after G160-01) needs them.
3. **G160-01, records:**
   - the tier 3 brief's dependency table (`briefs/fill-ram-classes.md`);
   - the dependency-walk requirement (`briefs/COMMON.md`);
   - the widened plan (`items/ram-tm/PLAN.md` §0: 32 admissions in four tiers);
   - the tier 0 brief (`briefs/fill-ram-steps.md`).

## Brief for the auditor

1. **G160-01:** check that the corrected tier 3 brief names every admitted declaration its
   prescribed routes reach. Check that the dependency walk it now requires can tell them apart.
2. **G160-02:** check the three docstrings against their statements.
3. **The vendored readers:** check that each restates its definition exactly, every `match` arm
   included. Check that the vendored header records the addition, and that the rest of the
   vendored file is byte-identical. Check that the four suffice for tier 0's 18 targets without
   unfolding `step`, `effect` or `Steps`.
4. **Rule 10 and standards** on the four new proofs; the evidence follows.

## Evidence (`evidence-r2/`)

- **`REPLAY.json`:** the merged-tree replay of the 5 owners' downstream closure on
  `oleans-cc91f4`.
  - 280 modules: 280 passed, 0 failed.
  - 42 inherited admissions, all pre-existing:
    - the 14 RAM admissions;
    - `Extended.lean`'s 18, now in the closure because `Steps.lean` changed;
    - 10 in BooleanAnalysis.
  - Pool 3; peak memory 3.8 GB.
- **Seals:** all 12 proofs pass. The four vendored readers reach no other-file definition
  (`Instr` is inductive), so they have no sealed heads.
- **Controls:** 20 definitions and 40 identities, each native-PASS and sealed-FAIL.
- **Sweeps:**
  - proof-syntax sweep: 12 roots, 0 read candidates;
  - Lean-backed sweep: no flag;
  - citation homes: SpaceComplexity/Basic, TuringMachine/Finite, TuringMachine/Nondeterministic
    and Programs/WordRAM/Basic.
- **Copy screen:** 0 → 0 pairs.
- **Earlier runs:**
  - **Run 1:** round 1's evidence, at `e75d2907`.
  - **Run 2** (`7ee903a4`, docstrings only): stopped at 30/265 when the vendored readers were
    added.

  Both are carried under `run1/` and `run2/`.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate160-ram-readers-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
