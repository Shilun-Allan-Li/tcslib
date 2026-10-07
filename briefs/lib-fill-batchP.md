# Machine-library fill campaign — Batch P: the primitive catalog

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-P`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-P.zip` with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

You are filling the fifteen primitive contracts of the machine-construction
library (`machine-library-design.md`; audit gate closed,
`audits/ch1-infra-resolutions.md`). The statements are **audited-true and
frozen absolutely** — each has a *Pass* verdict with the auditor's
realizability notes (`audits/ch1-infra-findings.md`, verdict rows 7–18 and
the supporting-checks section; `audits/ch1-infra-r2-findings.md`, items
8–9 for P13/P14/C1 and the P5/P10 sketch corrections). Those notes are
your route confirmations; read them before writing a machine. Roughly
half the targets are **harvests**: a proved private construction exists
in-tree and your fill adapts its definition and proof to this contract
(you may read any file; you modify only the owned file and never cite
another module's privates — re-derive in-file).

The binding discipline the audit stressed everywhere: **output is
append-only, so nothing is emitted until validity is known** — every
parser/extractor buffers on a work tape and replays after the separator
or length check validates (round-1 verdict rows 12–16).

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` — targets, in
  this fill order (easy harvests first, dependent targets last):
  1. `computesFunInTime_prepend` (1 pt — harvest: `prefixTM`/
     `prefixTM_computes`, `ClassNP/Reductions.lean:286–369`)
  2. `computesFunInTime_pairEncodeFixed` (1 pt — harvest:
     `fixedPair_computes`, same file at 369; it *is* prepend at the
     doubled-word-plus-separator prefix)
  3. `computesFunInTime_pairDup` (2 pts — two input passes, no buffering;
     round-2 item 9)
  4. `computesFunInTime_incFixed` (2 pts — harvest: `enumCarryTM`/
     `enumCarry_correct`, `ClassNP/EXP.lean:289–397`; two passes:
     overflow detection first, then emission)
  5. `computesFunInTime_pairValid` (2 pts — aligned two-bit scan in
     finite control, one verdict bit at the end)
  6. `computesFunInTime_pairFst` (3 pts — undouble onto a work tape,
     replay after the separator validates; misalignment halts silent)
  7. `computesFunInTime_pairSnd` (2 pts — same scan, copy the suffix)
  8. `computesFunInTime_pairConcat` (2 pts — P6's scan, replay buffer
     then suffix)
  9. `computesFunInTime_lengthBits` (3 pts — input scan driving an
     in-place binary counter, amortized constant per cell; emit the
     counter word; empty input yields `Nat.bits 0 = []` and still halts)
  10. `computesFunInTime_polyUnary` (4 pts — harvest: `polyUnaryTM`/
      `poly_unary_computes`, `ClassNP/TMSAT.lean:144–506`, **with the
      round-1 finding-5 indexing**: loop parameter `e − 1` for `e > 0`;
      a fixed `replicate C true` emission chain for `e = 0`)
  11. `computesFunInTime_polyBits` (2 pts — the unary clause composed
      with your length counter via the public
      `Turing.FinTM.computesFunInTime_comp`; the round-2 audit's
      composition calculation at the end of `ch1-infra-findings.md`
      confirms the exponent survives)
  12. `computesFunInTime_pairLenCheck` (3 pts — parse both components to
      tapes, lay down the polynomial in unary of `|a|`, countdown
      compare against `|b|`, one verdict bit; malformed answers
      `[false]`)
  13. `computesFunInTime_stripLast` (3 pts — parse, one reverse sweep to
      the last `true`, then emit the re-encoded pair; all-`false` and
      malformed halt silent; `Turing.splitAtLastTrue` is the spec)
  14. `computesFunInTime_pairMapSnd` (4 pts — parse silently; run `Mg`
      on the payload relocated-and-captured; emit doubled `a`,
      separator, captured `g b`. Monotonicity converts `|b| ≤ |z|`; the
      capture-tape payload length is bounded via
      `Turing.MultiTapeTM.output_length_le`)
  15. `computesFunInTime_splitSolve` (4 pts — **an
      `exists_loopFindTM` instance**, per the audited sketch's instance
      data: unary candidate state, the stall step keeping
      `Inv w s := |s| ≤ |w| + 1` step-closed, acceptance by the length
      equation, payload the encoded split, fuel `R n = n` with
      `Nat.bits n` supplied by your own length counter as `F`. The
      round-2 findings item 8 carries the full consistency check,
      including the `A(n+1)^(e+1)` body envelope and the final
      `2c(A+1)(n+1)^(e+2)` budget arithmetic.)

## Sanctioned `sorryAx`, this batch only

Batches W and L run concurrently. Per the epoch-2 precedent, exactly two
admitted roots are sanctioned, each through a **frozen, audited
statement**:
- `computesFunInTime_pairMapSnd` may show `sorryAx` **solely** through
  `Turing.capture_run` (batch W) — *if* your relocated-capture argument
  factors through it; a self-contained private adaptation of the
  2A/2B relocated-capture pattern (public `bufferTape`/`virtualMove` API)
  needing no admitted root is equally acceptable and preferred.
- `computesFunInTime_splitSolve` may show `sorryAx` **solely** through
  `Turing.FinTM.exists_loopFindTM` (batch L) — this one is the audited
  route; use it.
All other targets must be admission-free. Verify every root as the
epoch-2 batches did (kernel-environment traversal;
`audits/programs/ch1-infra-BuildSpecAxioms.lean` and the traversal in
`…-BridgeExportAxioms.lean` are committed templates) and report them.

## Environment and verification

As batch W: pinned toolchain, `lake exe cache get` once, **never
`lake build`**; bootstrap the 57-module order list; iterate the owned
module (position 26) plus later modules; final full 57-module fresh
sweep, zero `error:` lines. Axiom prints for all fifteen targets: at
most the standard triple, `sorryAx` only per the two sanctioned roots
above, root-verified.

## Ground rules (binding; `workflow.md` §4 in full force)

Exclusive ownership; `private` helpers, all listed; **statement freeze —
these contracts closed an adversarial gate; escalation over alteration**;
docstrings stay (append-only notes allowed, disclosed); precise imports;
no out-of-scope sorries. **34 points — continuation budget anticipated**
(the B2 precedent): if exhausted, deliver a partial zip stating the
frontier exactly, remaining targets' `sorry`s intact and listed. Lint 0
FAIL; the file will grow well past the 600-line target — keep it under
1000 if feasible, else record the justification in `REPORT.md`.

## Out-of-scope sorries you will see (leave untouched)

The 4 Wrappers and 4 Loop contracts (concurrent batches W and L); the
three TMSAT `D-*` sites; `enumMachine_contracts`/`EXP_subset_NEXP`;
`mem_NP_iff_exists_length_le`; the `Nondeterminism.lean` cluster;
everything in `SAT.lean`, `Tautology.lean`, `CookLevin/*`.

## REPORT.md checklist

- [ ] Fifteen targets filled in order (or the continuation frontier
      stated exactly); per target: the construction named, the harvest
      source acknowledged where one exists, and the buffer-before-emit
      obligation's discharge point named for every parser/extractor.
- [ ] Base hash recorded; all new private declarations listed.
- [ ] The two sanctioned roots called out and root-verified — or "unused".
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints.
- [ ] Diff touches only `Build/Primitives.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (`briefs/ch2-epoch1-batchA.md`
§pitfalls), plus:
- `pairEncode x α` doubles the **first** argument; `pairEncodeFixed α`
  computes `pairEncode α x` — the fixed word is the doubled one. Get the
  direction from `TuringMachine/Encoding.lean:113`, not from memory.
- `pairFst`/`pairSnd` return `getD []` — parse failure and a genuinely
  empty component coincide **by design** (round-1 verdict row 12);
  don't "fix" it, the guard stage is `pairValid`.
- `Turing.incFixed` is little-endian with `none` exactly on all-true
  words, including `[]`; the catalog function is `(incFixed x).getD []`.
- `Turing.solveSplit` uses `==` inside `find?`; your bridge lemmas will
  want `Nat.beq_eq` early.
- `splitAtLastTrue` drops the trailing false-run via
  `reverse.dropWhile (fun b => !b)` — prove your machine against its
  equations, not against an informal "last true" reading.
- The unary generator's budget `(C + 1 + 5r)·(n+1)^r` is per loop depth
  `r` — with the `e − 1` harvest indexing the total lands inside
  `c·(n+1)^(e+1)`; don't re-derive the harvest's arithmetic, adapt it.
- `Nat.bits` needs `import Mathlib.Data.Nat.Bits` (already in the file).
