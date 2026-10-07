# Machine-library fill campaign — Batch P3: primitives closure (targets 14–15)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-P3`), record
  the base commit hash in `REPORT.md`. The required base is
  `b2f464197cfd071ff46b3f89aa611285d3983908` (the integrated state after
  the P2 and L2 deliveries — **this is the exact integrated base the P2
  continuation document defers to**).
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-P3.zip` with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`. Package the archive **flat** (no
  wrapper directory), with `SHA256SUMS` at its root.

## Context

The closure batch of the machine-construction library's primitive
catalog: two targets remain of twenty-three contracts, and **every
dependency either target could want is now a proved theorem**. Three
documents are binding, in order: the original `briefs/lib-fill-batchP.md`
(ownership, freeze, verification protocol), `briefs/lib-fill-batchP2.md`
(the per-target routes for 14–15), and the P2 agent's own frontier
document at `audits/ch1-lib-agent-reports/batchP2-continuation.md` —
read it first; it inventories the proved target-14 assets waiting
in-file and states the two traps this brief repeats below.

State changes since P2, both in your favor:
- **The loop is complete** (batch L2 integrated): `loopHost_contracts`
  is proved and `Turing.FinTM.exists_loopFindTM` prints the clean
  standard triple. `splitSolve`'s audited route is now a fully proved
  theorem — **this batch sanctions zero admissions**; on completion the
  owned file has zero `sorry`s and the whole `Build/` tree is
  admission-free.
- The in-file target-14 assets are proved and integrated:
  `catalogPair_inverse`, `catalogPayload_length`,
  `catalogPayload_computes` (the explicit
  `bufferedCompTM (pairExtractTM false true) Mg` machine at
  `6(n+1) + Tg n + 1`), `catalogRewind`, and the `lenStart`
  host-instantiation example for `capture_run`.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` — targets, in
  order:
  14. `computesFunInTime_pairMapSnd` (4 pts). Build the threaded-map
      controller on top of the proved assets: one viable route (the
      frontier document's) captures the proved total payload machine
      `catalogPayload_computes` on the original input via `capture_run`
      (adapt the `lenStart` instantiation pattern to this host — do not
      pretend its `pairCountTM`-specialized endpoint already supplies
      it), silently validates and recovers the encoded first-component
      prefix (`catalogPair_inverse`), and replays prefix, separator,
      and captured output. The brief-P2 direct
      parser-plus-relocated-capture route is equally acceptable. Prove
      the exact phase seams and the total `c·(n + 1 + Tg n)` bound.
  15. `computesFunInTime_splitSolve` (4 pts). The audited — now fully
      proved — `exists_loopFindTM` route, instance data fixed in the
      target docstring and `machine-library-design.md` §9b: unary
      candidate state; `Inv w s := |s| ≤ |w| + 1`; append-or-stall
      step; acceptance by the length equation; payload the encoded
      split; fuel `R n = n` from the proved `lengthBits` witness,
      enlarged to the common body envelope `T n = A(n+1)^(e+1)`. Your
      construction obligations are the **body machine** discharging
      `hstart`/`hround`: startup to the empty-candidate seam, each
      candidate round (evaluate `|s| + C(|s|+1)^e` via the in-file
      generator against a countdown of `|w|`, emit the payload on
      acceptance, restore scratch and append on rejection), the
      anchor-entry discipline including time zero at startup and the
      strict interior for rounds, and a **positive-time silent stall**
      beyond the final candidate. Then the bridges: the unary-orbit
      identification (`(List.replicate i true).length = i`,
      `Nat.beq_eq` for `solveSplit`'s `==`), `List.range.find?` to the
      least solution, and the closing exponent-`e+2` arithmetic
      (`audits/ch1-infra-r2-findings.md` item 8 carries the checked
      calculation `c(A(n+1)^(e+1)+1)(n+2) ≤ 2c(A+1)(n+1)^(e+2)`).

## The two traps, repeated from the frontier document (binding)

- **No coarse composition bound for target 14**: `Tg (5(n+1))` is not a
  constant multiple of `Tg n` for arbitrary monotone `Tg`; use the
  proved actual-payload bound (`catalogPayload_length` +
  `catalogPayload_computes`).
- **The invariant admits arbitrary bit patterns** unless you strengthen
  it and prove the strengthened version: a target-15 round that uses
  lengths must preserve existing bits when appending or stalling —
  or strengthen `Inv` to all-true words and discharge `hInv0`/`hInvStep`
  for the strengthened form explicitly.

## Admissions

**None.** Both targets, every new helper, and on completion the entire
owned file must be admission-free; all twenty-three library contracts
then print at most the standard triple. Update the shipped
`verification/PrimitiveAxioms.lean` expectations to empty root sets for
all fifteen targets, and verify by kernel-environment traversal as the
previous deliveries did. Any `sorryAx` anywhere in the batch is a
defect.

## Environment, ground rules, out-of-scope

As the previous briefs, unchanged: pinned toolchain (Lean 4.25.0,
`cdd38ac5115b`; mathlib `029db123ddaa`), `lake exe cache get` once,
**never `lake build`**; bootstrap the 57-module order; iterate the owned
module (position 26) plus later modules; final full fresh 57-module
sweep, zero `error:` lines. Exclusive ownership; privates listed;
**statement freeze absolute; escalation over alteration**; docstrings
stay (append-only notes). **8 points; continuation again if exhausted.**
The file carries a recorded size exception (2,504 lines at base) —
report the final size; do not move code out of the file. Out-of-scope
sorries still visible on the branch: the 28 campaign admissions listed
in the original brief (nothing in `Build/` remains out-of-scope — the
other three files are fully proved).

## REPORT.md checklist

- [ ] Both targets filled (or the frontier exact); target 14's phase
      seams and bound derivation named; target 15's
      `hF`/`hInv0`/`hInvStep`/`hstart`/`hround` mapped
      hypothesis-by-hypothesis to your lemmas, stall round included.
- [ ] Base hash; all new private declarations listed; final file size.
- [ ] Axiom prints: all fifteen targets on at most the standard triple;
      zero `sorryAx` tree-wide in `Build/`; traversal expectations
      updated and passing.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `Build/Primitives.lean`.
- [ ] Archive flat, `SHA256SUMS` at root.

## Known pitfalls at this pin

The P and P2 lists carry over verbatim, plus:
- `exists_loopFindTM`'s conclusion applies `out x` to the **orbit
  word**; your payload equation goes through the replicate-length
  bridge before `w.take`/`w.drop` appear.
- The find conclusion's failure value is `[]` and `splitSolve`'s
  failure is also `[]` — the shapes align, but prove the `none` branch
  of `solveSplit` against fuel exhaustion explicitly (no solution in
  `0…n` ⟺ `find?` misses ⟺ the orbit never accepts within fuel).
- `hround`'s advance clause demands the **exact** seam equation
  `Cfg.ofWords anchor (stateWord k (stepF w s))` — scratch restored,
  heads at origin, output empty; the body's own invariant run backwards
  is the intended restore proof, per the frozen design decision 9.2.
- The stall round past the end must be silent, positive-time, and
  anchor-free in its strict interior — a two-step excursion returning
  to the identical seam is the simplest shape that satisfies all three.
