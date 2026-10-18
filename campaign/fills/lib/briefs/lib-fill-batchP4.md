# Machine-library fill campaign — Batch P4: library closure (`splitSolve` body)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-P4`), record
  the base commit hash in `REPORT.md`. The required base is
  `494d48353d292cca5d90675f5421f1bce09068e3` (the integrated state after
  the P3 checkpoint — **the exact base the P3 frontier document defers
  to**).
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-P4.zip`, **flat** (every member at the ZIP root, `SHA256SUMS`
  at the root), with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

One target closes the machine-construction library: the combined body
machine for the split search. Everything else is done — 22 of 23
contracts are proved, and for this one, `splitSolve_of_body` (proved,
in-file) already derives the public theorem from exactly two missing
arguments: the body's `hstart` and `hround` proofs. The proved component
inventory is substantial: preparation (`splitPrepare_run`/`_first`),
counted evaluation (`splitCount_*`, `splitPoly_loop_end`, and the
constant-exponent route via `catalogPrefixTM`), exact rejection
restoration landing on the literal seam
(`splitRestore_run`/`_first`), the orbit/search/failure/payload bridges,
and the closing exponent arithmetic.

**Four documents are binding, in order**: `briefs/lib-fill-batchP.md`
(ownership, freeze, verification), `briefs/lib-fill-batchP2.md` and
`briefs/lib-fill-batchP3.md` (the target's routes and traps), and —
read it first — the P3 agent's frontier document at
`audits/ch1-lib-agent-reports/batchP3-continuation.md`, whose
**"Work still required" section is your work plan**: ten numbered steps
from the combined finite body through applying `splitSolve_of_body` and
rerunning the checks with empty root sets. Its component descriptions
(exact seam configurations, flags, head positions, bounds) are the
interface you assemble against; its closing paragraph's four
prohibitions are restated below as binding.

## Owned file and target

- `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` — one target:
  `computesFunInTime_splitSolve` (5 pts), by constructing the combined
  body and discharging `splitSolve_of_body`'s two hypotheses. The ten
  steps, compressed:
  1–2. The combined finite controller (candidate on tape zero, disjoint
      control phases, helpers private) and its genuine startup seam —
      an anchor start state with empty initial candidate may give
      startup time zero, but the exact `Cfg.ofWords` equation must be
      proved.
  3–4. Embed preparation, hand its first-return endpoint to counted
      evaluation (configuration seam proved field by field: tape
      ordering, initialized source bank, zero work heads, native head
      at `splitPos`, flag, empty output), and discharge the
      `splitCount` table-agreement arguments for both exponent cases
      (`e = c + 1` for the positive case — not an off-by-one loop
      depth; the `catalogPrefixTM` constant route for `e = 0`).
  5–7. Branch on the checked acceptance predicate with the native-input
      rewind; **on acceptance, build and prove the payload emitter for
      `pairEncode (w.take s.length) (w.drop s.length)` — the one
      genuinely new machine piece** (the frontier document is explicit:
      the candidate is a length counter only; emit native-input bits,
      never candidate bits); on rejection, identify the configuration
      with `splitRestoreScan k w s 0` and map the checked cleanup's
      return to the anchor.
  8. The global round properties: positive duration and strict-interior
      anchor exclusion **across every phase** — the standalone
      first-return lemmas do not compose into this by themselves; prove
      the combined statement.
  9. One common body envelope `A·(n+1)^(e+1)`: candidate length via the
      invariant, evaluation via `catalogPolyCost_le`, plus the
      completed controller's actual scan/emission overheads.
  10. Apply `splitSolve_of_body`, delete the admission, set **every**
      expected root in the axiom program to empty, and re-verify.

## Binding prohibitions (the frontier document's, restated)

- No coarse-composition bounds (the recorded `Tg`-inflation trap).
- No weakening or restating of any frozen statement.
- No silent strengthening of the invariant to unary words — it admits
  arbitrary bit patterns; the proved components already preserve them
  (the past-end case is a silent stall on the same word, not a
  normalization).
- The conditional `splitSolve_of_body` is not a body construction; only
  the combined machine's proofs close the target.

## Admissions

**None.** On completion: zero `sorry` tokens in the owned file; all
fifteen primitive contracts — and with them all **23 library
contracts** — print at most the standard triple; the whole-`Build`
kernel traversal (the shipped `PrimitiveAxioms.lean`, expectations set
to empty everywhere) passes. Any `sorryAx` anywhere in the batch is a
defect. If the budget exhausts, deliver a checkpoint that shrinks the
frontier per the established discipline — but at one target with this
component inventory, completion is the expectation.

## Environment, ground rules, out-of-scope

As the previous briefs, unchanged: pinned toolchain (Lean 4.25.0,
`cdd38ac5115b`; mathlib `029db123ddaa`), `lake exe cache get` once,
**never `lake build`**; bootstrap the 57-module order; iterate the owned
module (position 26) plus later modules; final full fresh 57-module
sweep, zero `error:` lines. Exclusive ownership; privates listed;
**statement freeze absolute; escalation over alteration**; docstrings
stay (append-only notes). The file is at 3,684 lines under its recorded
exception — report the final size. Out-of-scope: the 28 campaign
admissions (nothing else in `Build/` remains admitted).

## REPORT.md checklist

- [ ] The target proved; the ten frontier steps mapped to your
      discharging lemmas, with the acceptance emitter and the global
      anchor/duration proof called out explicitly.
- [ ] Base hash; all new private declarations listed; final file size.
- [ ] Axiom prints: all 23 library contracts on at most the standard
      triple; the whole-`Build` traversal with empty expectations
      passing; zero `sorryAx` tree-wide in `Build/`.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `Build/Primitives.lean`.
- [ ] Archive flat, `SHA256SUMS` at root; working branch `fill/lib-P4`.

## Known pitfalls at this pin

The P/P2/P3 lists carry over verbatim, plus the frontier document's
specifics:
- `splitPrepare_first`/`splitRestore_first`/`splitCount_firstHalt` are
  **first-return** facts for their standalone machines; your host
  embedding must intercept exactly those returns
  (`catalogFirstEntry` is the shared absorption argument).
- The rejection endpoint is byte-exact:
  `Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s))` — map
  that state to your anchor rather than re-deriving the cleanup.
- The native head after preparation is `splitPos w s.length`, with a
  flag recording past-end; `splitCount_accept` needs blank native input
  **and** no overflow for the equality — keep both signals.
- The emitter's output is `pairEncode` of *native* slices: doubled
  `w.take s.length`, separator, `w.drop s.length` verbatim; its budget
  joins the body envelope at step 9.
- Startup time zero is legal only if the initial configuration *is*
  the seam — empty candidate, blank scratch, heads home; otherwise
  prove the positive-time startup with the anchor-free guard including
  `t' = 0`.
