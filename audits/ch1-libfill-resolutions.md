# Machine-library fill audit — resolutions. GATE: CLOSED

Single round (`audits/ch1-libfill-{pack,bundle}.md` →
`audits/ch1-libfill-findings.md`): **0 blockers, 0 majors, 2 minors —
gate condition met**; both minors are instrument/documentation issues,
swept in this closing commit. With this gate, the machine-construction
library is **complete and audited end to end**: the 23 statements closed
a three-round adversarial spec gate (`audits/ch1-infra-resolutions.md`),
and their proofs — eight fill commits, 282 explicit private
declarations — now close the companion proof gate in one round.

## The audit's positive findings (recorded)

The auditor independently re-derived, from source: the complete loop-host
time ledger (the per-component table, the `max 1 (max 9 10)) = 10`
constant, the free-initial-entry/zero-fuel case, and the
unreachable-terminal dispositions — explicitly confirming no amortization
and no logarithmic factor); the capture lockstep's write-before-move and
halting-emission handling; the split body's global `splitSafe` trace
argument (confirming it does **not** infer a global first return from
per-subroutine lemmas), its native-bit emitter (`|s|+|w|+3` recomputed),
and the envelope `A = (C+1+5e)·2^e + 40` including the degenerate cases;
the constants 5 and 40 with the explicit check that the forbidden
arbitrary-`Tg` substitution is absent (while noting, correctly, that
fixed-polynomial coarse bounds elsewhere are legitimate); harvest
fidelity by normalized text comparison of all 20 generator declarations
plus the `e = d + 1` indexing, the `incFixedTM` redesign, and the
`timeConstructible_id` witness (`c = 5`, empty input included); the
parser family's validate-before-emit discharge at every claimed point,
including that `stripLast` tests the **parsed payload** for the marker;
and helper hygiene over the full inventory (the one literal restatement,
`splitSolve_closed`, judged a disclosed visibility wrapper, not a hidden
assumption).

## Closing sweep (the two minors)

| # | Finding | Sweep |
|---|---|---|
| 1 | The decision form's proof-sketch paragraph still said `Turing.loop_run` sums the seam family (one site my R3-1 sweep missed), and pointed at the amortized borrow | Documentation correction in `Build/Loop.lean`, explicitly recorded here as the authorized maintainer closing-sweep edit: the sketch now names the private `loop_halted_run` with the R3-1 rationale, and the borrow sentence points at the worst-case-width estimate. Comment-only (comment-stripped file verified byte-identical); the module re-elaborates clean. |
| 2 | The closure program's success message claimed "the Build tree carries zero admissions" though it traverses only the 23 target closures (+ regressions); unused privates are outside its scope; stale checkpoint comments | `audits/programs/ch1-libfill-ClosureAxioms.lean` corrected: the header and success message now state the target-closure scope and name the P4 whole-Build traversal as the separate whole-tree instrument; stale comments replaced. Re-run on the integrated tree: PASS, exit 0 (`audits/logs/ch1-libfill-close-axioms.log`). |

## Dispositions (final)

* **D6 — approved as deferred** (finding 11): both `timed_input_bound`
  and `timed_rewind` judged promotion-worthy (the auditor confirmed the
  boundary cases); promotion proceeds as a separate serial API change
  after this gate, preserving hypotheses and field-preservation
  conclusions, replacing private copies only after the promoted lemmas
  and clients elaborate. Tracked in `backlog.md`.
* **D7 — approved as trailing** (finding 12): the split of `Loop.lean`
  (2,693) and `Primitives.lean` (4,418) trails the gate and the E2
  consumption, as a serial ride-along-audited refactor, **with the
  auditor's qualification adopted as binding for that refactor**:
  byte-identical relocation alone does not handle cross-file private
  use — keep dependent private families together or make any new
  cross-file interface an explicit, separately reviewed visibility
  change; then re-run the order sweep, target closures, whole-Build
  traversal, and kernel-export inventory. Tracked in `backlog.md`.

## Evidence limits (finding 10, recorded)

The auditor corroborated every current-source and final-log claim
(public counts, zero admission tokens, the 57/57 sweep recount with
exactly 28 non-Build admissions, the closure-program semantics and its
log) and explicitly qualified the **historical** attestations (the
whole-span freeze, per-delivery checksums/replay, the 33→30→29
progression, the integration decision-log entries) as maintainer
execution records not reproducible from the bundle. Those records exist:
the git history (`e346139c…c013f270`), the eight delivery archives under
`ch1_local/infra/` (local), the per-integration decision-log rows, and
the committed per-round logs. Disposition: recorded as evidence limits,
not findings; any future re-audit wanting independent historical
sign-off should be handed the baseline tree, the whole-span diff, and
the archives.

## What closes, what opens

Closed: the machine-construction library, end to end — specification
(three adversarial rounds), implementation (W: 1 round; L: 2; P: 4), and
proof audit (1 round, this record). The `Build/` tree carries zero
admissions; the campaign tree stands at exactly the 28 Chapter-2
admissions. Opens: the **E2 continuation briefs** (the four frozen
Chapter-2 frontiers against the proved toolkit), per the library
design's original sequencing; queued behind the gate: the D6 promotion
merge and the D7 split, both serial and ride-along audited.
