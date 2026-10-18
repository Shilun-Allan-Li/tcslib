# Emitter-increment fill gate — resolutions

**GATE CLOSED (2026-10-05). PASS in one round: 0 blockers, 0 majors,
2 minors, 7 notes** (`audits/emitter-fill-findings.md`). No proof
defect in the seven contracts or the 271 private helpers. The
auditor re-derived the bridge ledger to the exact `(24 + 13k)`
coefficient from the three phase bounds, verified `emLoop_sum`'s
shifted induction with the frozen `loop_run` untouched and
`emit_run` uncited (comment-stripped whole-source checks), confirmed
P2's `0 < j + 1 < t` dispatch inequality under equal entry/exit,
checked **harvest fidelity at 108 of 110 compared declarations
identical** after comment/whitespace/prefix normalization (both
divergences examined: a tactic swap on an impossible equality; the
sound generalization inside `emitter_binary_check`), confirmed the
271-name inventory in both directions with zero removals and no
foreign-private or admission mechanism, and corroborated with
35,000+ finite transition-table transcriptions. **The emitter
increment is complete and audited end to end**: statements (three
adversarial rounds) → fills (W 1, P 2 incl. continuation, L 1
round) → proof audit (one round).

## Errata (the two minors, swept here)

1. **The final attestation log's stale success sentence**
   (`audits/logs/emitterP2-axioms.log` line 28): the summary clause
   "the six remaining spec contracts … at their own roots" is the
   earlier partial-integration expectation; the declaration-level
   lines above it — all seven `ROOTS …: []` — are the result. The
   historical log is preserved as sent; the checker's message is
   corrected for future runs to say all seven emitter roots are
   empty with only the named campaign frontiers retaining roots.
2. **Span-attestation wording** (`audits/evidence/emitter-fill/
   span-attestation.md`, three corrections, evidence unchanged):
   - `d7b5b6f9` is the **whole-span starting commit**; P2's own
     pinned continuation base was `08884731`, as its brief and
     REPORT state.
   - The `FinCases` addition is **one newly imported module at two
     import sites** (`Loop.lean:7`, `Primitives.lean:9`), both
     disclosed — not one merged line.
   - Wrappers at 739 lines is **under the 1,000-line ceiling**, above
     the 600-line target (the lint log says so); Convention is under
     target. The 0 FAIL / 2 WARN result stands.
3. **Carried phrasing precision** (finding 8, accepted): the pack's
   "recorded actual clamped displacement" must be read subject to the
   standing R3/§11d correction — the implemented tracking family
   records **visited intervals and origin markers**, not a
   displacement or overwritten-symbol history; virtual clamping rides
   the template's `bufferedSecondCfg_run`/`VirtualTag` interface.

## Attestation-scope qualifications (finding 9, accepted as stated)

The auditor verified the final logs' contents, the current sources,
the inventories, and the harvest comparisons; the historical freeze,
per-delivery replay executions, intermediate sweeps, and kernel runs
remain maintainer attestations resting on the committed per-step
records — consistent with every prior gate's treatment, with no
contrary evidence found.

## Standing dispositions

No new dispositions. Loop 5,713 / Primitives 7,636 lines continue
under the recorded D7 trailing-split deferral (the post-E5
re-measurement and the single reviewed internal-namespace proposal
remain the plan). The deferred dedup of the local relocation/summation
helper families (noted by the auditor as consistent with policy)
joins that same serial queue.

## Downstream unblocking

With this gate, **every dependency of the remaining chapter-2
construction work is proved and audited**: A-cont-3 (padding targets
1/6/3/4/5, mostly `splitSolveWith` instantiation), 3B-cont (the
streaming reduction on `exists_emitLoopTM` + the clean calls, under
the r2-validated normalized schedule), and 4A (the Cook–Levin summit,
under the r3-certified stage mapping, the inherited boundary table,
and the `R`/`R+1` and chunk-rule clarifications).
