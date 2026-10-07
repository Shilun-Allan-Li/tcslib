# Machine-library fill campaign — Batch P2: primitives continuation (targets 12–15)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-P2`), record
  the base commit hash in `REPORT.md`. The required base is
  `90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee` (the integrated checkpoint
  state — batch P's eleven fills, batch W complete, batch L's checkpoint
  are all already on the branch).
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-P2.zip` with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

This is the continuation of batch P (`briefs/lib-fill-batchP.md`, **still
binding in full** — ownership, statement freeze, verification protocol,
and its per-target guidance for targets 12–15). The checkpoint
(`audits/ch1-lib-agent-reports/batchP.md`) filled targets 1–11 in order,
admission-free; your frontier is targets 12–15, the threaded and search
forms. The integrated file already contains the checkpoint's 54 private
helpers — **build on them, do not rebuild**: the shared `pairExtractTM`
parser and its `extract_*` invariant family, the `scanCfg`/`scanCopy_*`
scan lemmas, and the `catalogPolyUnaryTM` generator family
(`catalogPoly_*` through `catalogPoly_unary_computes`) are proved in-file
assets.

Two facts changed since the original brief, in your favor:
- **`Turing.capture_run` is now proved** (batch W, integrated). Citing it
  adds no admission. Batch W's own conditional controller
  (`Build/Wrappers.lean`: `timedCondTM`, `timed_capture`, `timed_rewind`,
  `timed_input_bound` and neighbors) is a proved in-tree template for
  instantiating it with a host controller — the pattern `pairMapSnd`
  needs.
- **`Turing.FinTM.exists_loopFindTM` has a filled (conditional) proof**
  rooted at the single admitted `Turing.FinTM.loopHost_contracts` (batch
  L's frontier, continuing concurrently as batch L2). `splitSolve`'s
  audited route through it therefore carries exactly that one root until
  the L2 merge closes it.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` — targets, in
  order:
  12. `computesFunInTime_pairLenCheck` (3 pts) — parse both components
      (the in-file parser), lay down `C·(|a|+1)^e` in unary
      (`catalogPolyUnaryTM` on the buffered `a` — note its budget is in
      the *buffer's* length, bounded by the input's), countdown compare
      against `|b|`, one verdict bit; malformed answers `[false]`.
  13. `computesFunInTime_stripLast` (3 pts) — parse, one reverse sweep to
      the last `true` (`Turing.splitAtLastTrue` is the spec; prove
      against its `reverse.dropWhile` equations), then emit the
      re-encoded pair; all-`false` and malformed halt silent.
  14. `computesFunInTime_pairMapSnd` (4 pts) — parse silently; run `Mg`
      on the payload **relocated** (public `bufferTape`/`virtualMove`
      API) **and captured** (instantiate the proved `capture_run` with
      your controller as host, per the batch-W template); emit doubled
      `a`, separator, captured `g b`. `Monotone Tg` converts
      `|b| ≤ |z|`; `Turing.MultiTapeTM.output_length_le` bounds the
      replay.
  15. `computesFunInTime_splitSolve` (4 pts) — **the audited
      `exists_loopFindTM` route**, with the instance data fixed in the
      target's own docstring and `machine-library-design.md` §9b: unary
      candidate state; `Inv w s := |s| ≤ |w| + 1`; the stall step;
      acceptance by the length equation; payload the encoded split; fuel
      `R n = n` with `F` obtained from your own proved
      `computesFunInTime_lengthBits` witness (`Nat.bits |x|` is exactly
      `Nat.bits (R |x|)` at `R n = n`). Your real work is the **body
      machine** discharging `hstart`/`hround` at a budget
      `T n = A(n+1)^(e+1)`: candidate evaluation via the in-file
      generator, countdown compare, payload emission, seam restoration
      (body-restores-scratch), the anchor-entry discipline, and the
      positive-time stall round past the end. The round-2 findings item
      8 (`audits/ch1-infra-r2-findings.md`) carries the full consistency
      check including the final `2c(A+1)(n+1)^(e+2)` arithmetic.

## Sanctioned `sorryAx`, this batch only

Exactly one admitted root is sanctioned:
`Turing.FinTM.loopHost_contracts`, reached **only** through the public
`exists_loopFindTM` in `splitSolve`'s proof (the audited route; batch L2
closes it at merge). Targets 12–14 must be admission-free. Verify every
root by kernel-environment traversal (the checkpoint's
`verification/PrimitiveAxioms.lean` and the committed
`audits/programs/ch1-infra-*.lean` are templates) and report them.

## Environment, ground rules, out-of-scope

As the original brief, unchanged: pinned toolchain, `lake exe cache get`
once, **never `lake build`**; bootstrap the 57-module order; iterate the
owned module (position 26) plus later modules; final full fresh 57-module
sweep, zero `error:` lines. Exclusive ownership; privates listed;
**statement freeze absolute; escalation over alteration**; docstrings
stay (append-only notes). **14 points; continuation again if exhausted.**
The file carries a recorded 1,687-line size exception — keep your
additions lean and report the final size; do not move code out of the
file. Out-of-scope sorries now visible: `loopHost_contracts`
(`Build/Loop.lean`, batch L2 concurrent) and the campaign admissions
listed in the original brief.

## REPORT.md checklist

- [ ] Four targets filled in order (or the frontier exact); per target
      the construction named, in-file assets reused named, and the
      buffer-before-emit discharge point named.
- [ ] For `splitSolve`: the instance data mapped hypothesis-by-hypothesis
      (`hF`, `hInv0`, `hInvStep`, `hstart`, `hround` — including the
      stall round and the anchor discipline) to your lemmas.
- [ ] Base hash; all new private declarations listed; final file size.
- [ ] The single sanctioned root called out and root-verified; targets
      12–14 shown admission-free.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints.
- [ ] Diff touches only `Build/Primitives.lean`.

## Known pitfalls at this pin

The original brief's list carries over verbatim, plus:
- The in-file parser (`pairExtractTM`) was built for emit-after-validate
  extraction; targets 12–13 need its *buffered components on work tapes*
  — reuse the invariant lemmas, not necessarily the machine verbatim.
- `catalogPolyUnaryTM`'s budget is a function of **its own input
  length**; when you run it on a buffered component, carry
  `|a| ≤ |z|` explicitly.
- `exists_loopFindTM`'s `hround` demands `0 < t` even for the stall
  round past the end — a one-step silent self-loop at the seam
  satisfies it; prove its seam equation exactly.
- The payload in the find conclusion is `out x` applied to the *orbit
  word*, which is `List.replicate i true` — your bridge lemmas go
  through `(List.replicate i true).length = i`.
- `Nat.beq_eq` early when connecting `solveSplit`'s `==` to the
  acceptance proposition.
