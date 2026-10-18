# MIG-0b gate: resolutions (round 1 → round 2; DRAFT)

**Gate:** MIG-0b, the second increment of the framed-contract library `Turing.Contract`
(`audits/mig0b-pack.md`; round-1 bundle SHA-256
`e0dc9e0ad89efe42b037a44ffcd6afe003d5746f6c10383972204c17a53cb66a`, 36 sections).
**Round 1** (`audits/mig0b-findings.md`, preserved verbatim): **0 blockers, 2 majors, 4 minors,
15 notes; does not close.** No proved statement was found false, and there is no counterexample to
the admitted existence statement.

**Round 2** is drafted by a maintainer sub-agent at campaign commit `1781a230`, against
`oleans-f8`. Its evidence is `audits/evidence/mig0b/r2/` (proposed paths; `BUNDLE-FILES.txt`):
- the landing unit, generated from the landed `Build/Contract.lean`, with 13 parts each
  cut-checked in its own import closure;
- the files the landing PR writes, in full;
- the fit file;
- the elaboration and axiom logs;
- the notes `NOTES-r2.md`.

*This draft is for the maintainer to review; it becomes the resolutions file when the gate's
round 2 is recorded.*

## Findings

| # | Severity | Finding | Resolution | Evidence |
|---|---|---|---|---|
| 1 | major | The planned split could not keep the proofs: private helpers (`mem_hull_left/right`, `runFrom_state_none_mono`) were used by seam proofs in another planned module; `counterLoopTMVia_done_witness` called the non-landing `MIG0bFit.counterLoop_hround_of_rounds`; the probe kept the fit helper and left out the seam consumers | **Repaired.** The three helpers are deleted, and their 12 uses cite public results: Mathlib's `Finset.Icc_subset_Icc` and `Finite`'s `MultiTapeTM.runFrom_state_ne_none_of_le`. The witness derives the round hypothesis locally from `Round.cut_some`. The split is now the draft: 13 landing parts, no `MIG0bFit` in the unit (asserted), each part elaborated in exactly its own import closure, the seam consumers in `Build/Contract/Seam` over `Contract/Basic` and `Build/Seam` alone. The revised plan is NOTES-r2 §3 | `elaboration.log` §2a (13 checks, 0 errors), §7 (acyclic graph; the core's closure is 5 modules); `identity.log` §3.2; NOTES-r2 §§2–4 |
| 2 | major | `seamReleaseTM_runFrom_pos` was restricted to `Type`, and its proof used a `Type`-only lemma, so it could not replace the polymorphic private `seamRelease_run_pos` | **Repaired.** The private lemma is promoted under that name with its universes (`Symbol S : Type*`) and its step-commutation proof, together with its two step lemmas (`seamReleaseTM_step_fresh`, `seamReleaseTM_step_inr`). Round 1's export is dropped. The consumers `seamReleaseTM_firstReturn` and `seamReleaseTM_visitedByTapeHead` keep their statements; only call sites change | `identity.log` §3.5 (30 Seam declarations, statements unchanged); `signatures.log` (18 of 18 public Seam types identical); fit file (round 1's statement an instance; a state carrier equal to `Type`) |
| 3 | minor | `Contract.lockstep`'s target entry is unconstrained; with an incompatible entry every application is vacuous | **Repaired.** New `Contract.lockstep_admissible` (entry compatibility gives admissible target starts) and `_map` (state-renaming encodings, `entry' = ρ entry`); the condition is stated in `lockstep`'s docstring. The source-start index is kept | Unit part 6; fit examples for the vacuous and the compatible case |
| 4 | minor | "Two live exits" overstated `RoundContract.release` | **Repaired** in the docstring: the escape set is arbitrary (`none`, several states, the anchor); two distinct live exits only for `{some e}` with `e ≠ anchor`; the phase host's no-halting and redirect conditions retained. The statement is unchanged | Unit part 8; two fit examples |
| 5 | minor | No literal proof sketch for the admitted `exists_alphabetReduction_lockstep`, and the intermediate controls must be live; `[AB09]` missing from the references | **Repaired.** A literal `**Proof sketch.**` covers the step equation with a halted source, offset `0`, the intermediate controls (live, never `arReady q`, so outside the renamed exit set for every `X`) and the halted source's offsets. The full [AB09] entry is in the section docstring, in `AlphabetReduction`'s References (already present) and in `Contract/Basic`'s References. The theorem stays admitted (RS-5) | Unit part 7; `axioms.log` (only this declaration and `alphabetReduction_contract` use `sorryAx`) |
| 6 | minor | Active records inconsistent: MIG-0 status and size, design item 4, F7-1(b)'s silent flavour, RS-5's alphabet milestone, the head-bound coordination | **Listed for the maintainer** (NOTES-r2 §10, nine corrections), not made. MIG-0's status was already corrected at `1781a230`; its size estimate was not. The head-bound coordination is evidenced: the fit file proves H2's exact `abs_workTapePos_runFrom_sub_le` statement from `workTapePos_runFrom_mem_Icc` | NOTES-r2 §10 |
| 7 | note | Segment obligations: no findings | Statements kept | — |
| 8 | note | Five segment fits: no findings; keep each row's quantitative conclusions when migrating | Kept; recorded for MIG-12, MIG-15, MIG-17, RS-3 | Fit file (unchanged) |
| 9 | note | Round statements: no findings; keep the find round's `7 * (length + 1)` bound; a round-time uniqueness lemma would help | Kept; the lemma is a recommendation (NOTES-r2 §12) | — |
| 10 | note | Counter loop: no findings beyond finding 1 | Finding 1's repair; conclusions unchanged | `identity.log` §3.4 (`counterLoopTMVia_done_witness`: proof edited, statement unchanged) |
| 11 | note | `Traj` and `Frames`: no findings | Unchanged | — |
| 12 | note | R1 family: no findings; the silent case is separate | Unchanged. fills-8 added a member, `RecordTable.rt_embed_matches` (over `Type*`), so the R1 lemma and its Embed neighbours are stated over `Type*` (NOTES-r2 §5) | Fit file (`rt_embed_matches`'s verbatim statement from `embedEmitCfg_eq`) |
| 13 | note | `mapState`, `liftSymbols`: no findings | Unchanged | — |
| 14 | note | Lockstep: no findings apart from finding 3 | Finding 3's repair | — |
| 15 | note | Alphabet admission: acceptable as an explicitly scheduled obligation | Kept admitted, with the sketch (finding 5); RS-5 milestone in §10; whether to land it before RS-5 is open question 1 | NOTES-r2 §11 |
| 16 | note | Sanity lemmas: no findings; positivity from the linked second contract optional | Recommendation | NOTES-r2 §12 |
| 17 | note | Identity and widths: no findings | Re-done against the landed file | `identity.log` §§3.1, 3.6 |
| 18 | note | Execution: logs consistent; separate replays not independently established | Re-run at `1781a230`; axioms over 201 public declarations; the landing replay remains | `elaboration.log`, `axioms.log` |
| 19 | note | Downward moves: statements fine, but this does not certify the split; preserve signatures, remove old copies, update the vendored-module notes; Basic about 1.3k lines | Moves verbatim. Homes: `runFrom_mapState_of_agreeOn` to `StateRenaming`; `spaceUsedByTape_le_card_Icc` to `Finite` instead of the vendored `Deterministic`, so no vendored file changes. Old copies deleted, checked whole in their own closures. Basic is 1,309 lines; no split, since size is not a driver and it is one import boundary | `identity.log` §3.3; `elaboration.log` §2b (extras 101–105) |
| 20 | note | No new duplication major; coordinate the head bounds; do not land fit copies | Fit copies do not land; one home per moved lemma; head bounds: finding 6 | — |
| 21 | note | Tactics stay descriptions; facade and `TCSlib.lean` wiring are landing obligations | Facade written (part 13); `TCSlib.lean` reaches it through `TuringMachine`, whose entry is updated | `landing/TCSlib/Complexity/TuringMachine.diff` |

## Rulings on the round-1 questions

| Q | Ruling | Disposition |
|---|---|---|
| 1 | Keep time-independent relations | Kept |
| 2 | Keep `SafeSegment` as a conjunction | Kept |
| 3 | Keep the live round interior | Kept |
| 4 | Keep the constant round index | Kept |
| 5 | General positive-cut contract useful, not a prerequisite | Recommendation (NOTES-r2 §12) |
| 6 | Keep the source-start index; add entry compatibility | Done (finding 3) |
| 7 | Guarded renaming to `StateRenaming`, with `Simulation` imported | Done; the closure is checked |
| 8 | Word reconstruction in `Embed`, which imports `Convention` | Done; the boundary is checked |
| 9 | Silent reconstruction: a capture-field export, deferred to MIG-14 as a named part | Recorded (NOTES-r2 §10 item 3) |
| 10 | Accept the deferred alphabet proof, with finding 5 repaired and RS-5 scheduled | Done; landing timing is open question 1 |
| 11 | `counterLoopOrbit` an abbreviation of `roundOrbit`; check the consumers | Done: 5 unfolding sites, of which 4 need a one-token edit (`CounterLoop`, `CfgRecord` ×2, `CodeSimulator`); `Inclusions` elaborates as is. Negative controls confirm the edits are needed (NOTES-r2 §6) |
| 12 | Keep the hulls; uniform corollaries where needed | Recommendation |
| 13 | Deferral acceptable; add `Frames.embed` before relying on it | Recommendation |
| 14 | Returning release through the pointwise equation after finding 2 | Done; statement and data fields unchanged |
