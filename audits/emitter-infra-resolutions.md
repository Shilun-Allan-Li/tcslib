# Emitter-increment shared-infrastructure gate — resolutions

**GATE CLOSED (2026-10-05). Three rounds:** round 1 **0/2/3**
(blockers/majors/minors), round 2 **0/2/1**, round 3 **0/0/1** —
`audits/emitter-infra{,-r2,-r3}-findings.md`. No false statement was
found in any round; every major was an adequacy or evidence
obligation, and all are discharged. The audited spec surface: **seven
sorried contracts** (`emit_run`; `exists_emitLoopTM`; the two
positive-tape clean-call bridges `exists_installCallTM` /
`exists_emitCallTM`; `computesFunInTime_splitSolveWith`;
`computesFunInTime_unaryToken`; `computesFunInTime_appendBit`), two
transformers, two vocabulary definitions. The round-3 verdict
authorizes treating the interface/customer-fit audit as closed — not
the seven admitted contracts as proofs: those are the fill batches'
work, under this record.

## The arc, for the record

- **R1** caught the adequacy gap no function-level contract can close
  (a witness may dirty scratch on its final transition) → the bridge
  contracts; and refuted the unchanged-host construction sketch with a
  one-state witness → the forwarding-host route.
- **R2** caught the zero-tape degeneracy (`stateWord 0 a =
  stateWord 0 b`; the install bridge satisfiable for arbitrary
  noncomputable `f`) → `0 < C.k` on both bridges; and refuted §11b's
  4A parser-validation framing with the empty-language witness →
  §11c's silent-preparation/ordered-emission mapping. It also
  validated the 3B normalization against the actual `satRedTM` table
  (5,908-case finite corroboration).
- **R3** certified both repairs (the projection-table derivation of
  the exported data interface; the stage-by-stage check of §11c
  against the inherited boundary table, including the exact chunk
  rule) and closed with one attribution minor, swept below.

## Minor swept in the closing commit

The install-call construction sketch attributed a proved
"log/undo" (overwritten-symbol history) implementation to the
A-continuation. What that delivery proves is **visited-interval
tracking and clearing** (`e3cTrackTM`/`e3cClearTM`) — and at a clean
entry seam that is sufficient: the module's scratch starts blank, so
clearing the tracked interval is the restoration, with no symbol
history needed. The docstring now says exactly this (verified
comment-stripped byte-identical otherwise), keeps the history/undo
route as the independently derived alternative (r2 finding 4), and the
design record carries the same correction (§11d).

## Binding on the fill batches and downstream briefs

1. **Fill obligations** (the seven contracts, partitioned by file
   ownership): Loop (`exists_emitLoopTM` via the **forwarding host
   variant** — body through `emitAction`, contracts over
   arbitrary-accumulated-output configurations, a **new**
   prefix-summation lemma, never the frozen `loop_run`; both bridges
   via the track/clear route at the r3-derived envelope); Primitives
   (`splitSolveWith` — evaluator on the **actual** length-`i`
   candidate, whole-canonical-word comparison, visited-region cleanup
   charged to elapsed time, never `TE` as a clock; `unaryToken`;
   `appendBit`); Wrappers (`emit_run` — mirror `capture_run`,
   forwarded halting emission).
2. **The 4A brief** inherits the phase-4 round-2 boundary-check table
   (`audits/ch2-phase4-reaudit-findings.md`) **verbatim**, plus from
   r3 finding 3: the `R` vs `R + 1` distinction (`R = n+(k+3)T+k+1`
   is the last round index and initial fuel; the member count is
   `R + 1`); the exact chunk rule `w_i` (per-member flatMap with the
   single terminator only on the last chunk — never the whole-formula
   serializer per group); the install call must receive the **packed
   preparation-record producer**, not a bare verdict; the emitting
   loop's budget bounds all startup/fuel/round work, not the tableau
   horizon `T`.
3. **3B-cont** builds on the r2-validated normalized schedule (state
   word = cursor/consumed-prefix/phase; no permanent marker;
   round-local buffering; absorbing finished phase; "token-bounded" =
   input-length-bounded, since a short token can trigger a large
   fresh-index emission).
4. **Provenance discipline**: the delivered continuation is a partial
   checkpoint; nothing in this gate treats it, or any admitted
   contract, as complete.
