# §12.7 counter-driven loops — statement-gate resolutions (CLOSED, round 1)

**Gate: CLOSED on round 1 (2026-10-10): PASS, 0 blockers, 0 majors, 1 minor,
5 notes.** Findings verbatim in `audits/s12-counter-findings.md`. The 13
definitions and 10 sorried theorems of `Build/CounterLoop.lean` (audited at
`e44b5656`) are true as stated, with no missing soundness hypothesis. This
commissions the fill batch.

## The auditor's evidence

- 23 blind restatements, recorded before reading the docstrings.
- Adversarial instantiations for every theorem, and deletion counterexamples
  for the necessary hypotheses.
- An independent executable model that compares whole represented tapes.
- The exact-time and amortization arithmetic re-derived.
- A consumer-fitness table for all four consumers.

## Dispositions

| Finding | Disposition |
|---|---|
| SC-1 (minor): `counterOverhead`'s "exact cost" needs its physical range | **Swept** (doc-only). The docstring now says the sum runs along the frozen word orbit and equals the physical countdown's cost only through the first underflow (`r ≤ value + 1`), which covers every use. No theorem change. |
| SC-2 (note): several `hround` conjuncts and `counterWord_value`'s bound are redundant, harmlessly | **Recorded; no change.** The auditor's caution is carried: the returning theorem's positivity and the interior anchor avoidance are *not* redundant. |
| SC-3 (note): the contracts are deterministic, and the NTIME consumer needs a nondeterministic lifting | **Carried** to design §12.7 as a prerequisite of the NTIME hierarchy fill: a choice-stream lifting contract with branch alignment. |
| SC-4 (note): wiring two continuations needs the private `seamComp_left` | **Carried** to design §12.7: promote `seamComp_left` (`Build/Seam.lean`) when the first two-continuation consumer is assembled; never copy it. Decision 12.7.2's "no new composition lemma" claim is corrected. |
| SC-5 (note): an optional visited-set or `spaceUsedByTape` corollary | **Offered** to the fill brief as an optional export. |
| SC-6 (note): keep evidence and certification distinct | Recorded. The fill gate runs the required checker and lint. |

## Next

The fill batch. Its brief is drafted once RB5 merges, so that the host proof
can cite the promoted `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`
(RB5 Task 1). ZF-B3's continuation (B4) follows the fill.
