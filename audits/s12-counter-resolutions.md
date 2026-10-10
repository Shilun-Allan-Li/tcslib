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

## Fill integrated (2026-10-10)

The fill batch (`briefs/s12-counter-fill.md`) delivered **10/10** at base
`c9a0b431`. It is integrated by `git am -3` as `2e99bda1`, with Codex
authorship; the agent's report is `audits/s12-counter-agent-reports/fill-REPORT.md`.

- **Routes followed:** one direct one-step symbol transport; **one** decrement
  run transport (`counter_decrement_run`) for both decrement contracts, with
  no trace; the auditor's telescoping potential; **one** round induction
  (`counter_rounds`) for both host theorems; and the body phase as one
  explicit step followed by guarded transport through the public RB5 lemma.
- **Freeze** (independent declaration-level check): 24 public declarations
  before and after. No statement changed, and exactly the ten theorem bodies
  changed. Two docstring appendices on the amortization theorems keep the
  original text as a prefix, as does the module status appendix. 25 new
  privates; imports unchanged.
- **Replay:** `Build/CounterLoop` and the `TuringMachine` facade both have
  0 errors and 0 sorries. Nothing imports `CounterLoop`.
- **Axioms** (`audits/logs/s12-counter-fill-axioms.log`): all 24 public
  declarations are within `[propext, Classical.choice, Quot.sound]`, several
  at proper subsets. No `sorryAx`.
- **Lint:** 0 FAIL. `CounterLoop.lean` is 1,205 lines, over the 1,000-line
  mark; the justification is in the plan's decision log.
- **Duplication:** the maintainer's run of the copy-text screen over
  CounterLoop, Catalog, Embed, Loop and StateRenaming reproduces the agent's
  after-output exactly (686 pairs, 282,786 characters). There is no new
  cross-file pair, and the four new in-file pairs all lie below 90%, each
  justified.

The fill rides a §12.7 fill-gate audit.


## Fill gate: pack issued (2026-10-10)

Pack `audits/s12-counter-fill-pack.md`, bundle `audits/s12-counter-fill-bundle.md`
(30 attachments). The maintainer's records are the freeze log, a fresh replay
at `5ad155ee`, the axiom prints, lint, the reproduced copy-text screen, and a
supplementary screen against Primitives, Seam, Wrappers and Simulation. The
supplementary screen shows no CounterLoop pair with Primitives (RB5's
`emitterP2_call_phase` pattern), and one short pair with Seam (59% of a
135-character step lemma), which the auditor is asked to rule on. Findings go
to `audits/s12-counter-fill-findings.md`. The gate closes on zero blockers and
zero majors.
