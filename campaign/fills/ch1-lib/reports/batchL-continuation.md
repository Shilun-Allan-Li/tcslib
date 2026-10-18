# Continue machine-library batch L

**Partial checkpoint, not a closed batch.** Read the committed
`briefs/lib-fill-batchL.md` on `complexity/arora-barak-ch1` first. Its statement
freeze, ownership, construction route, and verification rules remain binding.

Base: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
Checkpoint: `769341f5bd042f5790f7a24fdfe9e439b32ff666`.
Only owned file: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.

The public target bodies are present, but the three combinators remain
conditional on the single private admission below. `loop_run`, both terminal
summation lemmas, and all non-capture helpers are admission-free. The three
capture helpers use only the sanctioned `Turing.capture_run` root. Preserve
all five original public declarations and existing docstrings.

## Exact remaining admitted declaration

```lean
private lemma loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool) (findMode : Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ c : ℕ, ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg (loopHost body F anchor findMode).k Bool
          (loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (loopHost body F anchor findMode).tm.runFrom
          ((loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) := by
  -- Continuation frontier: the controller is defined, but its phase assembly,
  -- canonical seam family, and uniform time ledger still require proof.
  sorry
```

This is an unproved **concrete-machine** contract. Neither the fact that the
controller typechecks nor the abstract summation lemmas discharge it. Do not
replace it by an untimed computability result or by another out-of-scope
admitted theorem. The two output modes deliberately share the same finite
controller: false gives fixed verdicts; true replays the full first payload.

## Controller and tape layout

The first `body.k` tapes are the body's work tapes. Tape `body.k` is the
one-cell stop-kind flag. Tape `body.k + 1` is the fixed-width counter. The
next `F.k` tapes hold fuel-machine work and are preserved after fuel. The
last tape, `body.k + 1 + (1 + F.k)`, captures fuel and then body output.
The fuel setup copies its captured bits into the counter while clearing the
capture tape; both heads are then rewound together.

The state space has distinct fuel states, body states tagged startup/active,
and `Fin 14` controller phases. `loopBodyTM` has an additional release bit:
true forces one source action; every successor clears it. An unreleased
anchor stops silently with flag `some false`; a genuine source halt sets
flag `some true` while retaining every source emission. This also distinguishes
acceptance with an empty payload from exhaustion.

| Phase | Transition responsibility | Existing proof |
|---|---|---|
| 0, 1 | Mandatory left move and rewind captured fuel to its origin | Pending |
| 2 | Copy fuel to counter while clearing the capture tape | Pending |
| 3 | Rewind counter and capture heads together under the counter word | Pending |
| 4, 5 | Rewind native input and dispatch to body startup | `loopHost_input_rewind` |
| 6 | Clear startup's false stop flag; release initial anchor for free | Pending |
| 7 | Read stop kind; accept or clear flag and debit | Pending |
| 8 | Fixed-width binary borrow | Standalone `loopBorrow_*`; host lifting pending |
| 9 | Successful borrow rewind; release next body seam | Standalone rewind; host lifting pending |
| 10 | Underflow rewind | Standalone rewind; host lifting pending |
| 11 | Emit false (decision) or nothing (find), and halt | Pending one-step assembly |
| 12 | Rewind the captured accepting payload | Pending |
| 13 | Emit captured payload verbatim and halt at the right blank | `loopHost_replay` |

## Recommended next proof obligations

1. **Relocations and fuel setup.** Use `rightCfg_run` twice to relate
   `loopFuelSource` to `F`, retaining initially blank body/flag/counter tapes.
   Choose the first fuel halt with `loop_first_halt`, use `loopHost_init` and
   `loopHost_fuel_capture`, then prove phases 0–3 with their exact scan lengths.
   `loopFrame`/`loopControl_apply` isolate the active track operations. Combine
   `loop_input_run_le` and the checked phase-4/5 rewind to preserve a budget
   in the fuel run's time, even when that time is sublinear in input length.
2. **Startup return and active body calls.** Lift `loopBodyTM` through
   `loopBodySource` using `leftCfg_run`, with arbitrary counter/fuel residue.
   Use the checked `loopBody_run` and actual-host `loopHost_body_capture`.
   Startup's no-anchor guard includes time zero; active rounds use release
   true and the strict-interior guard. Rejecting endpoints imply no prior
   halt or output (`loop_live_prefix`, `loop_silent_prefix`). For acceptance,
   replace a padded endpoint by its first halt before applying W1.
3. **Host counter lifting.** Prove that actual phases 8–10 implement the
   standalone decrement, preserving every non-counter track and native
   input position. The exact standalone cost is `2 * loopBorrowPos u + 2`,
   bounded by `2 * u.length + 2`. Phase 11's final emission is an additional
   part of the last rejecting segment, not a separate unbudgeted round.
4. **Acceptance completion.** Prove flag dispatch and the payload rewind
   before applying `loopHost_replay`. `loop_output_length_le` charges the
   payload length to the original body round because its starting output is
   empty. Fixed-verdict mode takes its one final emission directly.
5. **Canonical configuration family.** At candidate index `i`, use the
   original body's `Cfg.ofWords anchor (stateWord body.k ...)`, host active
   release state, blank stop flag and capture tape, and counter word
   `((fun w => (loopDebit w).1)^[i] (Nat.bits (R x.length)))`. Its width and
   value at `i ≤ R x.length` are already proved. Retain the completed fuel
   work tapes and their heads. Thread `loop_orbit_inv` before every body call.
6. **Terminal choice and budget.** At the last rejecting candidate, use the
   actual underflow-plus-emission endpoint for the halted terminal. If that
   candidate accepts, use any halted terminal with the required false/empty
   output. Prove local contracts even for seams unreachable after an earlier
   acceptance. Include `R = 0` and empty binary fuel explicitly. Sum the
   proved startup/body/counter/dispatch constants and use the audit's single
   maximum constant. No completed uniform bound is claimed in this checkpoint.

The corollary proofs should then close without additional construction work.
Do not use frozen `loop_run` directly for the `[false]` terminal;
`loop_halted_run` is the checked lemma for that case. `loop_find_run` already
proves the exact `List.range.find?` output, including an empty selected payload.

## Reproduction and closure

The ZIP contains the one-file patch and prerequisite-based bundle; integrate
without overwriting concurrent W/P changes. Use Lean 4.25.0 and the committed
mathlib pin. Never invoke `lake build`.

From the repository root, with the pinned `lean` on `PATH`, set
`TCSLIB_OLEANS` to a new writable directory and run the included
`verification/sweep.py` (or the committed shell-script loop). Run
`verification/run_axioms.py` with the same variable. The scripts take the
repository from the working directory, or `TCSLIB_REPO` if provided.

At this checkpoint, `verification/Axioms.lean` explicitly expects the private
construction root. After filling it, change the expectations for all three
combinators and for `loopHost_contracts` to the actual sanctioned W1-only root
(or none, once W1 is merged and proved). Once W1 itself is proved, also change the three capture-helper expectations
to empty. Keep every other closed-helper expectation empty. Re-run a fresh full 57-module sweep, all root checks, lint, statement
freeze, and checksum generation. The current 1,466-line file size needs the
recorded ownership justification, or a separately authorized refactor after
this batch; do not move code out of the owned file during the continuation.
