# External audit pack — the emitter increment, round 3

Round 2 (`audits/emitter-infra-r2-findings.md`): **0 blockers, 2 majors,
1 minor** — round-1 findings 3–5 closed; the bridge construction
validated at the strengthened interface (r2 finding 4) and the 3B
normalization validated against the actual `satRedTM` table with a
5,908-case finite corroboration (r2 finding 5). The two cumulative
majors and the minor are repaired here. The round-1 and round-2 packs
are immutable and stand; the design record of this round's repairs is
`machine-library-design.md` **§11c**. Gate closes on **zero
blockers/majors** across cumulative findings. Record findings in
`audits/emitter-infra-r3-findings.md`.

## Repairs under audit (map to round-2 findings)

1. **Finding 1 (major) → `0 < C.k` on both bridges.** Both existential
   conclusions in `Loop.lean` now carry the positive tape count, with
   docstring rationales naming the empty-domain degeneracy
   (`stateWord 0 a = stateWord 0 b`) and your zero-tape witness. Your
   finding 4 already established that the log/undo construction
   delivers this strengthened interface at the stated envelope; what
   remains is to certify the repaired statements discharge the
   cumulative R1-1/R2-1 adequacy obligation — the seam equality now
   yields genuine `bufferTape` content at index zero for both install
   and emit modes.
2. **Finding 2 (major) → §11c's corrected 4A mapping, superseding §11b
   item 3 in full.** The parser-validation framing is withdrawn (your
   empty-language witness is recorded in §11c; parse-before-emission
   belongs to 3B/4B only). The corrected mapping follows your required
   repair: a **silent startup packs the s1–s5 preparation records into
   `s0 x`** (exact arithmetic with certificate length never enlarged;
   virtual reference input `false^m` with clamped head and
   halting-transition writes through the capture/install interfaces;
   inclusive trajectory over all times `0..T` with administrative
   transitions outside simulated time; greatest-strictly-earlier
   visits with sequential comparison costs) — all ending with empty
   physical output and the packed records as the clean persistent
   word; then **one family member per round** over the fixed family
   order, `R = n + (k+3)·T + k + 1` from your family counts, empty
   template rounds at positive duration, the single final terminator
   on the last chunk, and the exact ledger
   `1 + 2·#clauses + Σ(v+3)` with total output `O_M(T²)`. The
   time-major `R = T` alternative is explicitly not adopted. The
   phase-4 **round-2 boundary-check table is now attached**
   (`audits/ch2-phase4-reaudit-findings.md`) — certify the mapping
   against it; the 4A brief will inherit that table verbatim.
3. **Finding 3 (minor) → the §11a item-1 supersession marker**, inline
   at the stale text, pointing to §11b item 6; history preserved as
   history.
4. **Your two narrower evidence limitations → provenance upgrades.**
   The log/undo fill route now has fresh, in-repo, delivered
   provenance: the **A-continuation checkpoint** (integrated
   2026-10-05, Codex commit, byte-identical replay) banked exactly the
   phase family your finding 4 describes — `e3cTrackTM`/
   `e3c_track_run`/`e3c_track_extent` (logged simulation over a
   contiguous visited interval with origin markers, the actual clamped
   displacement recorded), `e3cClearTM`/`e3c_clear_run` (exact
   single-triple cleanup within `6T + 7` at a positive first return),
   `e3cCompareTM` (whole-optional-word comparison with rewinds), and a
   captured prepared-evaluator phase with first-halt dispatch — all as
   proved privates. Its REPORT and full source are attached; the
   phase-4 reaudit record closes the other gap.

## Maintainer attestations (verify or challenge)

1. **A-continuation integration** (context, not under this audit): the
   checkpoint banked 69 proved privates with zero new admissions; net
   deletion = one docstring tail line (append-only appendix); both
   shipped sources byte-identical under replay; the six padding
   targets and all out-of-scope admissions byte-identical; the
   agent-disclosed base-hash discrepancy was a **maintainer brief
   erratum** (a hand-expanded short hash; recorded in the decision log
   with the process correction).
2. Combined fresh 57/57 sweep over the A-continuation integration plus
   this round's repairs: zero `error:` lines, admissions
   **20 = 13 campaign + the 7 spec contracts**
   (`audits/logs/e3contA-r3-sweep.log`, attached).
3. The epoch-2 closure regression program re-run with full prints at
   the repaired tree, exit 0, every expectation unchanged
   (`audits/logs/emitter-r3-axioms.log`, attached).
4. This round's repairs pinned as a patch
   (`audits/evidence/emitter-infra/r3-repairs-commit.patch`, attached);
   the only non-documentation statement change is the `0 < C.k` clause
   in the two bridge conclusions.
5. Lint on `Build/`: 0 FAIL / 2 WARN, the standing size exceptions
   (`audits/logs/emitter-r3-lint.log`, attached).

Severity scheme as always; findings to
`audits/emitter-infra-r3-findings.md`; this pack is immutable once sent.

## Bundle manifest

**36 attachments** after the pack: the 4 `Build/` sources (Loop
repaired this round); the 5 model files; the design document
(§11–§11c); the 3 grammar files; the 4 customer files; the 2 epoch-3
frontier REPORTs (A, B); the **A-continuation REPORT**
(`audits/ch2-epoch3-agent-reports/batchA-cont.md`) and
**`ClassNP/Nondeterminism.lean`** (the `e3c*` provenance); the 2
phase-4 records **plus `ch2-phase4-reaudit-findings.md`**; the prior
infra-gate record; the closure program; the lint program; the **3**
pinned spec-commit patches (round 1, round 2, round 3); the 3 round-3
logs; the 57-module order list; the round-1 **and** round-2 findings.
Total 4+5+1+3+4+2+2+3+1+1+1+3+3+1+2 = 36.
