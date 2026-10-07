# Ch2 fill campaign — E2 continuation, Batch A: discharge `enumMachine_contracts`

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2cont-A`),
  record the base commit hash in `REPORT.md`. The required base is
  `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2cont-A.zip`, **flat** (`SHA256SUMS` at the root), with
  `REPORT.md`, the full modified source, the `git format-patch` series, a
  git bundle, the final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context — what changed since your predecessor's checkpoint

The original `briefs/ch2-epoch2-batchA.md` and the checkpoint record
(`audits/ch2-epoch2-agent-reports/batchA.md`) remain binding context. The
enumerator batch reduced `NP_subset_EXP` to the **single admitted private
`enumMachine_contracts`** (`TCSlib/Complexity/ClassNP/EXP.lean`, the
file's one in-scope `sorry`, ≈ line 764). Since then the campaign built,
audited (three adversarial statement rounds + a proof round, both gates
CLOSED), and fully proved a **machine-construction library**:
`TCSlib/Complexity/TuringMachine/Build/{Convention,Wrappers,Loop,
Primitives}.lean` — 23 public contracts, zero admissions. Your fill is
its flagship customer: **the audited route for `enumMachine_contracts`
is an instantiation of `Turing.FinTM.exists_loopCfgTM`**, certified
exactly at the customer's statement by the infra round-3 audit
(`audits/ch1-infra-r3-findings.md`, item 5: terminal index
`2^w = R + 1`, bounded orbit bridge, budget domination — "no
customer-statement edit or replacement decider theorem is needed") and
recorded in `machine-library-design.md` §9b–§9c. Read those two records
first; they are the route, and they are binding.

## Owned file and target

- `TCSlib/Complexity/ClassNP/EXP.lean` — one target: the private
  `enumMachine_contracts` (7 pts). Its statement is **frozen** (it is the
  audited continuation interface; the outer `NP_subset_EXP` proof already
  consumes it). On completion, `NP_subset_EXP`, `HALT_NPHard`, and
  `HALT_not_mem_NP` all print the clean standard triple — your REPORT
  includes all three prints.

## The binding route (§9b/§9c + round-3 item 5)

Write `w := C * (x.length + 1) ^ c`. Instantiate `exists_loopCfgTM` with:

- `Inv x s := s.length = w` — the exact-width invariant;
- `s0 x := List.replicate w false`; `stepF x s := (incFixed s).getD s`
  (overflow stalls, preserving width — `hInvStep` is immediate);
- `acceptF x s` := the verifier's verdict on `x ++ s`, realized inside
  the body by a **captured run of `MV`** (the hypothesis machine);
- fuel `R n := 2 ^ w - 1`: `Nat.bits (2 ^ w - 1) = List.replicate w true`
  (prove this identity as a private bridge lemma), so `hF` is discharged
  by the library's `computesFunInTime_polyUnary C c` **directly** — the
  fuel machine is a catalog instance;
- the **body machine** is your construction: from the seam (candidate on
  tape 0, scratch blank), assemble `x ++ s` on a buffer, run `MV`
  relocated-and-captured (`Turing.capture_run` with your controller as
  host; the proved `pairMapTM`/`timedCondTM` layers in `Build/` are
  in-tree instantiation templates), read the verdict; on acceptance halt
  `[true]`; on rejection restore scratch (the assembly buffer's extent is
  known, `n + w`), increment the candidate in place (the `incFixed`
  carry discipline; the superseded in-file `enumCarry*` lemmas may be
  consulted as templates but see the no-touch rule below), and return to
  the seam — positive time, anchor-free interior, per the loop contract.

Then translate the loop conclusion onto the frozen statement: the orbit
bridge `∀ i < 2^w, (stepF x)^[i] (s0 x) = enumWord w i` by induction from
the **in-file, proved** `enumWord_zero`, `enumInc_word`, and the
`incFixed = enumInc` equality (round-2 vocabulary note; both definitions
are in scope here); the configuration family and per-round clauses map
index-for-index (`cfg (2^w)` is the exported terminal); the budget
`b * (n + w + 1) ^ e` dominates `c' * (T n + 1)` once your body envelope
`T` is a polynomial in `n + w` — round-3 item 5 carries the full
derivation including width zero. Follow it; do not re-derive a different
translation shape.

## Rules on the superseded in-file privates

`EXP.lean` contains the checkpoint's `enumCarryTM`/`enumCaptureTM`/
`enumLoop_run` families, now superseded by the library. **You may ignore
them or cite them (they are proved and in-file); you must not remove,
rename, or modify them** — deduplication is a recorded E5 closure task.
Your new helpers are `private`, named distinctly, and listed.

## Sanctioned `sorryAx`

**None.** Everything this fill consumes is proved: the full library, the
in-file enumeration semantics, Chapter 1. On completion the file's only
remaining admission is the out-of-scope `EXP_subset_NEXP` (epoch 3).

## Environment, ground rules, verification

As the original E2 brief, with one update: the committed module order is
now **57 modules** (`scripts/ab_ch1_module_order.txt` — the four `Build/`
modules joined it). Pinned toolchain (Lean 4.25.0, `cdd38ac5115b`;
mathlib `029db123ddaa`); `lake exe cache get` once; **never
`lake build`**; bootstrap the 57-module order; iterate
`TCSlib/Complexity/ClassNP/EXP` plus later modules; final full fresh
57-module sweep, zero `error:` lines. Exclusive ownership; statement
freeze absolute; escalation over alteration; docstrings stay
(append-only notes); kernel-traversal root verification
(`audits/programs/ch1-libfill-ClosureAxioms.lean` is the committed
template). 7 points; continuation per the B2 precedent if exhausted.

## Out-of-scope sorries you will see (leave untouched)

`EXP_subset_NEXP` (epoch 3); `mem_NP_iff_exists_length_le` (2C-cont,
concurrent); the `Nondeterminism.lean` cluster (2B-cont + epoch 3); the
`TMSAT.lean` `D-*` sites (2D-cont, concurrent); everything in E3/E4
files.

## REPORT.md checklist

- [ ] `enumMachine_contracts` proved; the instantiation mapped
      hypothesis-by-hypothesis (`hF` via the catalog fuel instance with
      the bits-identity bridge; `hInv0`/`hInvStep`; `hstart`; `hround`
      with the capture, restore, and increment phases named) and the
      conclusion-translation steps mapped to round-3 item 5's derivation.
- [ ] Axiom prints: `enumMachine_contracts`, `NP_subset_EXP`,
      `HALT_NPHard`, `HALT_not_mem_NP` — all at most the standard
      triple, root-verified empty.
- [ ] Base hash; all new private declarations listed; final file size
      (the file has a recorded 600-line-target overrun; report the new
      figure).
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail; diff touches only `EXP.lean`; archive flat.

## Known pitfalls at this pin

The original E2-A list carries over verbatim, plus:
- `exists_loopCfgTM`'s round hypothesis demands `0 < t` and the
  strict-interior anchor clause — your restore phase is part of the
  round, not free.
- `Nat.bits (2^w - 1)`: prove the replicate identity by induction on
  `w`; do not unfold `Nat.bits` numerically.
- The orbit stalls at the all-true word only **beyond** fuel — within
  fuel, `incFixed` always succeeds; keep the `getD` fallback out of the
  bridge's induction (it never fires for `i < 2^w - 1`... and at the
  last point the bridge needs no successor).
- The library seam pins the input head at 1; your assembly scans must
  rewind it before the seam return (`timed_rewind`'s pattern in
  `Build/Wrappers.lean` is the proved template).
- Budget translation: choose your body envelope as a polynomial in
  `n + w + 1` from the start; round-3 item 5 shows `b = K(A+1)`,
  `e = D` — pick coefficients once, after `C, c, a, d` and before `x`.
