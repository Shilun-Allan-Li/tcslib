# Machine-library fill campaign — Batch W: the wrappers

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/lib-W`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-lib-W.zip` with `REPORT.md`, the full modified source, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

You are filling the four wrapper contracts of the machine-construction
library (`machine-library-design.md`, audited through three adversarial
rounds — gate closed, `audits/ch1-infra-resolutions.md`). The statements
are **audited-true and frozen absolutely**: every contract survived
independent refutation attempts, so a statement you believe is wrong is an
escalation, never an edit. All four have round-1 audit verdict *Pass* with
the auditor's realizability notes recorded in
`audits/ch1-infra-findings.md` (statement-verdict table, rows 1–4, and the
"Convention, wrapper, and primitive checks" section — read both; they are
your route confirmations). This batch has **no admitted dependencies**:
everything the sketches cite is proved.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean` — targets, in order:
  1. `Turing.capture_run` (4 pts)
  2. `Turing.FinTM.redirectTM_computes` (2 pts)
  3. `Turing.FinTM.redirectTM_live` (2 pts)
  4. `Turing.FinTM.computesFunInTime_cond` (6 pts)

## Targets and their binding routes

1. **`capture_run`** — one induction on `t`. The step case applies the
   agreement hypothesis and `Turing.Action.apply` componentwise: first `k`
   tapes and input head exactly as the source; the capture tape appends
   the emitted bit at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`
   is the rewrite); host output stays `out₀`; a live successor maps through
   `emb`, the halting transition lands on `ret` **after** that transition's
   emission is captured. The liveness guard supplies exactly the needed
   "source stepped for real" fact at each `t' < t`. Harvest templates (all
   proved, in-tree — adapt, do not cite privates):
   the private capture engine in
   `TuringMachine/Composition.lean` (≈ lines 479–553), `acceptCfg_step`/
   `acceptTM_run` in `ClassNP/Reductions.lean` (≈ 170–253),
   `enumCapture_step`/`enumCapture_run` in `ClassNP/EXP.lean` (≈ 423–555),
   and the public `universalCaptureTM` layer in
   `TuringMachine/UniversalStartup.lean` (from line 405).
2. **`redirectTM_computes`** — lockstep correspondence carrying the
   register invariant (register = last emission so far, `none` before
   any); at the source's halting transition the register equals
   `w.getLast?`, which matches `haltOn`, so the redirect halts there with
   everything suppressed; absorb to `t` with `ComputesInTime.mono`.
   Harvest: `acceptTM_halts_iff` and its invariant family
   (`ClassNP/Reductions.lean:170–253`) — note the register there updates
   **before** the halt test; keep that order.
3. **`redirectTM_live`** — same lockstep to the halting transition; the
   mismatched register sends control to `Sum.inr ()`, and the stationary
   live state is fixed by every further step (two-line induction, the
   `acceptTM_loop` pattern).
4. **`computesFunInTime_cond`** — build the conditional machine: run `D`
   under your own capture discipline (now available: instantiate
   `capture_run` with your controller as host), rewind the input head
   (`Turing.FinTM.rewind_from_any`; the head moved at most `T₀ n` cells,
   so the rewind is budgeted by the decider's run — the auditor's note on
   verdict row 4), dispatch on the captured bit into
   `Turing.FinTM.branchTM` (public, `TuringMachine/Simulation.lean`), and
   run the selected branch from its genuine initial configuration on the
   shared physical input. No monotonicity hypothesis exists — do not
   smuggle one in; the branch sees the original input.

## Environment and verification

Pinned toolchain (Lean 4.25.0, release commit `cdd38ac5115b`; mathlib
`029db123ddaa` via the committed manifest); `lake exe cache get` once;
**never `lake build`**. Bootstrap the 57-module order
(`scripts/ab_ch1_module_order.txt`) once with
`scripts/lean_check_tree.sh`; after edits re-check the owned module
(position 10) and everything after it; final **full 57-module fresh
sweep, zero `error:` lines**. **Axiom prints** for all four targets: at
most `[propext, Classical.choice, Quot.sound]` (subsets fine); **no
`sorryAx` anywhere in this batch** — there is no sanctioned dependency.
`audits/programs/ch1-infra-BuildSpecAxioms.lean` is the print template.

## Ground rules (binding; `workflow.md` §4 in full force)

Exclusive ownership of the one file; helpers `private`, every new
declaration listed in `REPORT.md`; **statement freeze on all existing
declarations — these statements closed an adversarial audit gate;
escalation over alteration, always**; docstrings stay (append-only
implementation notes allowed, disclosed); precise imports; no
out-of-scope sorries touched. 14 points; continuation per the B2
precedent if exhausted. Style lint must stay 0 FAIL (every remaining
`sorry` keeps a sketch; your proofs keep the house comment density).
Keep the file under 1000 lines if feasible; if ownership forces beyond,
record the justification in `REPORT.md` for the maintainer's decision
log.

## Out-of-scope sorries you will see (leave untouched)

The 4 Loop and 15 Primitives contracts (concurrent batches L and P); the
three TMSAT `D-*` sites; `enumMachine_contracts`/`EXP_subset_NEXP`
(`EXP.lean`); `mem_NP_iff_exists_length_le` (`NP.lean`); the
`Nondeterminism.lean` cluster; everything in `SAT.lean`, `Tautology.lean`,
`CookLevin/*`.

## REPORT.md checklist

- [ ] Four targets filled, with the induction/invariant route named per
      target and the harvest sources acknowledged.
- [ ] Base hash recorded; all new private declarations listed.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints (at most the triple; zero
      `sorryAx`).
- [ ] Diff touches only `Build/Wrappers.lean`.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (`briefs/ch2-epoch1-batchA.md`
§pitfalls, same pin), plus:
- `Turing.Action.apply` writes at the **current** head position, then
  moves; the capture-tape head arithmetic in `captureCfg` is calibrated
  to that order.
- The capture tape's no-emission case is `(none, SignType.zero)` — no
  write **and** no move; don't normalize it to a blank write.
- `captureCfg`/`captureAction` use `dite` on `(i : ℕ) < k`; keep your
  case splits on the same `dite` to avoid `Fin.castSucc` coercion fights.
- `redirectTM`'s register is `Option Bool`: `none` means "no emission
  yet" and never equals `some haltOn`; a source with empty output loops
  forever regardless of `haltOn`.
- `Cfg.ext` needs all five fields; for zero-work-tape hosts use
  `Cfg.ext_zero_tapes`.
- Output is append-only: `Action.apply` appends `a.output.toList`; the
  silence clause is `output := none`, never "emit blank".
