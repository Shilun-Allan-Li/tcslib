# External audit pack — Chapter 2, Phase 1, round 3 (final gate check)

Audits commit `79128c7a` on `complexity/arora-barak-ch1`. Round 2
(`audits/ch2-phase1-reaudit-findings.md`, audited at `8660c416`) reported
**zero blockers, 3 majors, 2 minors, 2 notes**, certifying the round-1
definition repairs (Arguments A/B/D dead; "no false Lean theorem statement";
all 19 statements sound) while faulting three sketches/prose passages. All
round-2 findings are repaired in this commit; **no Lean statement changed** —
this round audits three sketch texts, one docstring, and the plan
synchronization. The gate closes on zero blockers/majors. Record findings in
`audits/ch2-phase1-round3-findings.md`.

## Resolution of the round-2 findings (verify each)

| Round-2 finding | Resolution in `79128c7a` |
|---|---|
| 1 major — Ex-2.1 reverse witness `C(n+1)^c + 1` not of the class's admissible shape | The (⇐) sketch in `ClassNP/NP.lean` now uses **the auditor's own construction**: exact length `R n = (C+1)(n+1)^c` (coefficient `C+1`, degree `c` — admissible), marker room `R n − C(n+1)^c = (n+1)^c ≥ 1`, split at the unique `n` with `n + R n = m`, last-`true` stripping, the original-bound check, and the two-directional witness correspondence with the round-2 edge-case coverage cited |
| 2 major — enumerator obligations omitted output isolation | The `NP_subset_EXP` sketch in `ClassNP/EXP.lean` now names the **verifier-call simulation** obligation verbatim from the finding: capture the decision bit in finite control, suppress physical emissions (append-only output; the `[false, true]` two-round violation is cited), redirect the verifier's halt to the loop controller, keep the real output empty until finalization, reset simulated state/heads/work region/captured bit between rounds, all inside the timed invariant; `Turing.universalCaptureTM` named as the in-repo precedent |
| 3 major — false "effectivity is necessary" justification | `HALT_not_mem_NP`'s docstring in `ClassNP/Reductions.lean` retracts the unlawful trivial-machine counterexample (it violates `decode_encode`) and restates the `EffectiveMachineCode` hypothesis as a **proof-route restriction** (the proof reuses Chapter 1's `HALT_not_computable`); the auditor's direct diagonalization is described and the generalize-or-keep decision is recorded as **human-review design question 1** in the Chapter-2 plan, with the maintainer's provisional conservative choice (do not grow the audited uncomputability surface inside a repair round). The theorem statement is unchanged |
| 4 minor — plan §2 and two decision rows stale | Plan §2's first two foundation bullets rewritten to the repaired state (explicit formulas; paired bounded side; the concatenation-bounded variant's `P = NP` equivalence recorded as a prohibition); the two pre-repair decision rows marked **Superseded** in place |
| 5 minor — pack attestation-3 count mixed categories | Erratum acknowledged in the decision log; the shipped round-2 pack is preserved as the historical artifact (standing precedent). This pack's attestation 3 counts definitions and theorem signatures separately |
| 6 note — statement repairs stand | No action; recorded |
| 7 note — evidence-scope guidance | Adopted: attestations below separate reproducible source facts from maintainer-side execution claims |

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Scope.** `79128c7a` touches exactly: three `ClassNP/` files (comment-only
   changes — docstrings and sketches), the Chapter-2 plan, and adds the
   round-2 findings file. **No Lean statement, definition, or proof term
   changed in this commit** (there are no proofs); the 19 `sorry` tokens and
   their distribution (3/2/4/3/7) are unchanged. Chapter-1 files untouched
   since their closed gates.
2. **Elaboration.** The three changed modules and the facade re-gated at
   `79128c7a`: fresh oleans, zero `error:` lines, admissions unchanged.
3. **Statement inventory** (categories separated, per round-2 finding 5): 10
   definitions and 19 theorem signatures; relative to the round-2 audited
   commit `8660c416`, **0 definitions and 0 theorem signatures changed**;
   3 docstrings/sketches changed (`mem_NP_iff_exists_length_le`,
   `NP_subset_EXP`, `HALT_not_mem_NP`).
4. **Policy.** Style lint: zero FAIL, six pre-existing Chapter-1 WARNs; every
   admission keeps its sketch; statement prose intact.

## Brief for the auditor

This is a narrow round; its whole surface is three sketch texts, one
docstring, and the plan synchronization.

1. Verify the resolution table row by row against the source.
2. **Re-check the adopted Ex-2.1 (⇐) construction** as transcribed into the
   sketch: is the sketch a faithful rendering of your round-2 derivation
   (admissible `R n`, marker room, unique split, last-`true` strip, original
   bound, both witness directions, edge cases)?
3. **Re-check the enumerator obligation list** for completeness one more time:
   with output isolation added, would a fill agent still hit an unnamed
   obligation?
4. **Re-read `HALT_not_mem_NP`'s docstring**: is the proof-route framing now
   accurate, the retraction complete, and the human-review pointer correct?
   (The design question's *disposition* is human-reserved and out of scope.)
5. Confirm the plan's §2 now matches the repaired foundations and that the
   superseded rows are correctly marked.
6. Assess attestations 1-4.

## Scope

| Item | Where |
|---|---|
| Files under audit | `ClassNP/NP.lean`, `ClassNP/EXP.lean`, `ClassNP/Reductions.lean` (changed docstrings/sketches only — all statements were audited in rounds 1-2), `AroraBarakChapter2Plan.md` |
| Context | `audits/ch2-phase1-reaudit-findings.md` (round 2 — your report), `audits/ch2-phase1-findings.md` (round 1), both round packs, `AroraBarakChapter1Plan.md`, `policy.md`; all 40 modules + root attached |
| Out of scope | everything already certified in rounds 1-2; the human-reserved design question's disposition; Chapter-1 mathematics; phase-2/3 design questions |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
