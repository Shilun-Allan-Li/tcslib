# External audit pack — U2, the `k`-tape universal machines (PR #168, a fill gate), round 2

**Round 1** (`findings.md`; resolutions `resolutions.md`): FAIL, 0 blockers, 1 major, 1 minor, 10
notes.
- **The major:** the review's edit D1 (`uk_loop_forward` citing `MultiTapeTM.exists_first_halt`)
  reads that lemma's prefix `∀ v < t₀, ¬ (…).Halted` as `state ≠ none`. That is a definitional
  use of `Turing.Cfg.Halted`. The landing seal did not cover it, and the coverage probe missed
  three new citations.
- **The minor:** `exists_selfUniversalK`'s sketch omitted the seam's one step.

**The user ruled (2026-10-26):**
- answer the major with the campaign's convention on reducible abbreviations, now written into
  the standards, and add the coverage;
- fix the minor on #168.

**The head:** `lean/u2-universal-landing` at `948df2f995e0d2a849ac79c51d88365f0db09848`. Since
round 1's head `fd995ec1` it has one docstring-only commit, `948df2f9`. Its Lean diff from the
campaign branch is still `UniversalK`, `SelfUniversal` and the `TuringMachine` facade. Since round
1 the campaign has merged #164 (`ClassNP/Transducer`, `ClassP/TimeConstructible`,
`SpaceComplexity/Basic`, `SpaceComplexity/Constructible`), which touches none of the three. This
bundle's Lean files are from `948df2f9`, and its records from the records commit that the
dispatch prompt names.

## Brief for the auditor

1. **The major.** `Cfg.Halted` is `abbrev Cfg.Halted cfg : Prop := cfg.state = none`
   (`TuringMachine/Configuration.lean:226`), reducible, with no `_iff` lemma.
   - **The seal cannot include it.** `evidence/round1/HaltedSealProbe-*` show that
     `attribute [local irreducible] Turing.Cfg.Halted` fails ("`Cfg.Halted` is currently
     `[reducible]`, `[semireducible]` expected"), and so does the route through
     `[local semireducible]`.
   - **The campaign's position**, unchanged and now stated in `policy.md` (*Definitions land with
     their lemmas*) and `campaign/standards/TEMPLATE.md` (seals and reducible abbreviations):
     reading a reducible abbreviation through its body is allowed and is not a definitional
     closure. A consumer names it in `simp`, `rw` or `unfold` only through a published lemma.
     The issued C1 core briefs already allowed exactly this reading
     (`campaign/fills/c1/briefs/c1-fill-core-cont1.md:239`), and gate 34 recorded it
     (`campaign/gates/34-brief-api/evidence/r3/gate-review-r2.md:119`).
   - **Check:** does any step of the delivered file or of D1–D3 unfold a **sealable** other-file
     definition, or pass `Cfg.Halted` (or any other definition) to `simp`, `rw` or `unfold`? Is
     the stated convention coherent with rule 10's purpose (proofs read definitions through
     their published API, so an implementation can change)? If you think it is not, say what a
     proof can do instead when Lean refuses to seal the abbreviation and no lemma exists.
   - **The coverage:** the worker's import probe extended by `MultiTapeTM.visitedByTapeHead_mono`,
     `FinTM.ComputesInTime.spaceUsed_le_of_halt` and `Cfg.Halted` gives 597 checks of 596 names,
     0 errors (`evidence/round1/LandingImportProbe.*`). Is every declaration the landing cites
     outside its file covered?
2. **The minor.** Is `948df2f9`'s sketch now an exact reading of the proof (the lockstep through
   the first halt `t₀ ≤ t`, then the seam's step: `T_α + 1 + D·t`)? Is the commit docstring-only?
3. **No regression.** The new head's `UniversalK` elaborates against `oleans-la1m` (the tree
   after #164), with both targets on the standard three axioms
   (`evidence/round1/UniversalK-948df2f9-ax.out`). Is anything else changed?
4. **Round 1's other points.** Is anything in round 1's resolutions unaddressed?

## Repository-side attestations (verify or challenge)

- **Elaboration and axioms:** as in item 3.
- **The seal probe:** `HaltedSealProbe-one-step` and `-two-step` (sources `.lean.txt`, outputs
  `.out`), against `oleans-la1m`. The attribute lines are refused, so the seal never takes
  effect and every example closes.
- **Freeze:** `948df2f9` changes only `exists_selfUniversalK`'s docstring (7 lines); code
  identical with comments stripped.
- **Replay:** `UniversalK`, `SelfUniversal` and the `TuringMachine` facade (3 modules), chained
  from the snapshot #167's replay leaves, after the campaign is merged in. **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/80-u2-universal-fill/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `u2-universal-fill-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
