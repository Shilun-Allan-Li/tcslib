# External audit pack — Chapter 2, Phase 4, round 2 (re-audit)

Audits commit `c3579472` on `complexity/arora-barak-ch1`. Round 1
(`audits/ch2-phase4-findings.md`, audited at `6484ce88`) reported **zero
blockers, 1 major, 2 minors, 5 notes**: no false definition or statement
anywhere; all five locality theorems certified (Derivation A), the tableau
correctness re-derived (Derivation B), design question (a) resolved
affirmatively (Derivation C), the DNF/TAUTOLOGY package verified
(Derivation D) — while the `SAT_NPHard` **emitting-machine** sketch omitted
the output-isolation/halt-redirection contract for its preparatory stages.
All round-1 findings are repaired in this commit; **no Lean statement or
definition changed** — the drift is two import lines plus docstring/sketch
text. The gate closes on zero blockers/majors. Record findings in
`audits/ch2-phase4-reaudit-findings.md`.

## Resolution of the round-1 findings (verify each)

| Round-1 finding | Resolution in `c3579472` |
|---|---|
| 1 major — the emitter sketch's missing output-silence/halt-redirection contract (concrete false positive: `[false] ++ serialize φ_x` fails exact consumption, decodes to the fallback `[] ∈ SAT`; a forwarded source halt strands the output at `[false] = serialize []`) | The `SAT_NPHard` sketch's stage (5) is rewritten around the **output-silence contract**, with your six-stage table adopted verbatim as stages (s1)-(s6): exact arithmetic with captured subroutine answers and empty physical output; virtual-input reference simulation (`List.replicate m false`, head clamped `0..m+1`, disjoint tapes, physical input still `x`); discarded source output with an **internal** halted flag and the frozen trajectory recorded to `T`; trajectory recording with administrative steps uncounted; last-visit comparison with sequential-scan costs; serialization with the invariant "physical output empty before serialization, exactly the serialized prefix after", halting only on completion. The sketch states both failure modes concretely, and marks the lockstep embeddings as usable components but **not** substitutes for the contracts |
| 2 minor — "accept when some clause-conjunct fails" (a DNF is false iff **every** term fails) | The `TAUTOLOGY_mem_coNP` sketch now reads "accept iff **every** term contains an unsatisfied literal, i.e. evaluate `evalDNF` and answer its negation", with the empty-term/empty-formula cases and the correction noted |
| 3 minor — `Hardness.lean` missing the imports of the cited normalization theorems | `import TCSlib.Complexity.ClassNP.TMSAT` and `import TCSlib.Complexity.TuringMachine.Robustness.Oblivious` added — both precede `Hardness` in the order list; no cycle; the module re-gates clean |
| 4 note — locality derivation guidance (strict `s < t`; no-write vs. write-blank distinct) | Retained; the fill inherits Derivation A's exhaustive write table, including `some none` erasing to blank and writes on the halting transition |
| 5 note — bitwise pinning needs a product encoding | The variables passage now specifies the **product** encoding (state code, then input-symbol code, then per-tape codes — fields as literal slices) with the totalized decoder, citing your note |
| 6 note — DNF congruence bridge fine as private fill lemma | Retained as a named obligation; no new public statement |
| 7 note — survey-row nuance | Adopted in the decision log: "un-auditable" reads as not audit-ready under this protocol as supplied; the effort comparison is an engineering estimate not excluding partial-reuse strategies |
| 8 note — evidence separation | Retained below |

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Scope.** `c3579472` touches exactly: `CookLevin/Hardness.lean`
   (two import lines + docstring/sketch text), `ClassNP/Tautology.lean`
   (comment-only), the plan (two decision rows), and adds the round-1
   findings file verbatim. **Statement drift, enumerated by the corrected
   comment-stripped recipe** (`audits/ch2-phase3-resolutions.md`, appendix):
   `Hardness.lean`'s stripped diff vs. `6484ce88` is exactly the two import
   lines; `Tautology.lean` is stripped-identical. 0 signatures, 0
   definitions changed; everything else byte-identical.
2. **Elaboration.** The repaired modules and both facades re-gated at
   `c3579472`; a full 53-module fresh sweep run at this commit: zero
   `error:` lines, zero gate failures, exactly **59** admissions,
   distribution unchanged (14 phase-4: 2/5/5/2).
3. **Policy.** Style lint: zero campaign FAIL; six Chapter-1 WARNs
   unchanged. All sketches intact; the repaired sketch keeps statement
   prose before it.

## Brief for the auditor

A narrow round: one rewritten sketch stage, one corrected prose phrase, two
imports, and the plan rows.

1. Verify the resolution table row by row against the source.
2. **Is the transcribed six-stage contract faithful to your table**, and —
   with it in place — is the emitting-machine obligation list now *complete*
   at statement phase? Would a fill agent following it still hit an unnamed
   contract (the round-1 test applied once more)?
3. Re-read the product-encoding passage and the exact length ledger: do
   they match your Derivations B-C, including the pinning-family cost and
   its absorption?
4. Re-read the corrected TAUTOLOGY phrase against Derivation D.
5. Assess attestations 1-3.

## Scope

| Item | Where |
|---|---|
| Files under audit | `CookLevin/Hardness.lean` (changed sketch/docstrings + two imports), `ClassNP/Tautology.lean` (changed prose only), `AroraBarakChapter2Plan.md` (the two new rows) |
| Context | `audits/ch2-phase4-findings.md` (round 1 — your report), `audits/ch2-phase4-pack.md`, the closed phases' audit records, both plans, `workflow.md`, `policy.md`, `scripts/ab_ch1_module_order.txt`; all 53 modules + root attached |
| Out of scope | everything certified in round 1 (the 14 definitions, all locality and DNF derivations, the acceptance family); closed gates; the human-reserved design question; fill-time constructions beyond obligation naming |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
