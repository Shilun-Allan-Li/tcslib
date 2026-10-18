# §12 fill campaign — Epoch F2, continuation A2: the loop ledger and the forwarding controller (`Build/Catalog.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Create your working branch off it (suggested name
  `fill/s12-f2-A2`), record the base commit hash in `REPORT.md`, never
  rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-s12-f2-A2.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

This is the **continuation of batch F2A** (the chapter-1 `universal` B2
precedent): the prior agent proved 17 of 19 targets and delivered a
documented frontier (`audits/routine-f1-agent-reports/batchF2A-REPORT.md`
— read it; its per-target section quotes the binding audit rows). Your
file now contains all F1 and F2A material: **306 F2A private helpers plus
the F1 helpers are yours to use** — in particular `f2_loopHost`,
`f2_loopHost_body_capture`, `f2_loopHost_prepare`, `f2_loopHost_round`
and companions (local copies of the received loop controller and its
phase contracts), `f2_loopHost_contracts`, `f2_segment_heads`,
`f2_seamed_space` (the reusable-seam time-window space argument), and the
`catalog_redirect*` family. Read
`briefs/routine-f2-batchA.md` for the full epoch context; this brief
narrows it to the two remaining targets.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Catalog.lean` — exactly two
targets, in this order:

1. **`Turing.FinTM.exists_loopTM_spaceUsed`** (the L row). The six-step
   answer-5 ledger quoted in `briefs/routine-f2-batchA.md` is binding.
   Per the F2A frontier: bound the source body positions from the space
   hypotheses, project those positions through each captured call, retain
   the fuel bank bound, and combine the fixed-width counter/capture and
   flag intervals. **No multiply-by-round-count space argument is
   acceptable** (the interval-union argument of answer-5 step 2 is the
   invariant's shape: per-tape unions over arbitrarily many rounds stay
   inside `[-S n, S n]`).
2. **`Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed`** (the summit —
   the §12 fill's only new machine). Build the commissioned forwarding
   controller; the received captured-output `pairMapTM` witness is
   **refuted** for this bound and must not be reused. Named construction
   obligations (F2A frontier + round-2 R4, all binding): the validating
   buffer stage; the encoded-prefix emission stage; the forwarding payload
   simulation with **both virtual-input boundary clamps, including the
   empty payload**; their seam; malformed-input rejection; the
   coefficient-one source-bank trajectory containment; the halted-tail
   bounds. The R4 ledger to land:
   `space ≤ Sg(|b|) + A(n+1) ≤ Sg(n) + A(n+1)` and
   `time ≤ B(n+1+Tg(|b|)) ≤ B(n+1+Tg(n))`, one `c ≥ max(A,B)`, with
   forwarded output never occupying a work tape and the inherited time
   clause proved verbatim for your witness.

## Environment and verification

As `briefs/routine-f2-batchA.md` (toolchain pin, `lake exe cache get`,
the 65-module bootstrap plus the five facade-wired modules, iterate with
`bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`).
Final: your file at **zero `error:` lines and ZERO `sorry` warnings** —
this delivery completes the §12 layer — then the `TuringMachine` facade
check. **Axiom prints** for both filled theorems: at most
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Ground rules (binding)

Identical to `briefs/routine-f2-batchA.md` (exclusive ownership of
`Catalog.lean` only; statement freeze over **all** existing material,
F1 and F2A proofs included; escalation on unprovable-as-stated; no file
split; docstring appendices flagged; `private` helpers only, all listed).
Continuation budget: if exhausted again, the same partial-delivery
protocol applies — but prefer delivering target 1 complete over partial
progress on both.

## REPORT.md checklist

- [ ] 2/2 filled; `Catalog.lean` zero-sorry (or the exact frontier).
- [ ] Base hash; every new `private` declaration listed; the controller's
      stage structure identified by lemma; the loop ledger's six steps
      mapped to lemmas.
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero error, zero sorry) + facade check +
      2 axiom prints.
- [ ] Diff touches only `Build/Catalog.lean`.

## Known pitfalls at this pin

All of `briefs/routine-f2-batchA.md`'s list, plus from F2A's delivery:
the `f2_loopHost*` copies expose the received controller's phases — use
their contracts rather than re-deriving the host; `f2_seamed_space`
already proves the reusable-seam window argument used by `splitSolve`,
and its shape transfers; the file is 9,404 lines by recorded
justification — navigate by declaration name, and do not reorganize.
