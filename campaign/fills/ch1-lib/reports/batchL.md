# Batch L — partial continuation checkpoint

**Status: PARTIAL. The full batch acceptance gate remains OPEN.**
`Turing.loop_run` is proved without admissions. The three finite-machine
combinators have derivations, but all depend on the single admitted private
`Turing.FinTM.loopHost_contracts`. That root is **not** the sanctioned
`Turing.capture_run` admission. This ZIP is a continuation delivery under the
brief's continuation clause, not a completed construction or a closed gate.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required source branch: `complexity/arora-barak-ch1` (cloned explicitly with `--single-branch`).
- Base: `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Local working branch: `fill/lib-L`, created from that base as the committed brief directs.
- Checkpoint: `769341f5bd042f5790f7a24fdfe9e439b32ff666`.
- Execution: `lib-L-20261003T191127Z`.
- Only changed tracked file: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.
- No remote branch was pushed; no PR was created; no other branch was modified.
- The brief, workflow §4/§6, policy, W environment protocol, epoch-1 pitfalls,
  round-1 construction notes, round-3 items 4–5, and enumerator harvest were read.

All five original public declarations, their signatures, and their order are
unchanged. `stateWord`'s implementation is unchanged. Every existing declaration
docstring is preserved verbatim. The module docstring receives only an appended
checkpoint-status paragraph. The only added import is `Build.Wrappers`, for W1.
No out-of-scope admission was edited. `verification/freeze.py` reproduces these
checks; `verification/freeze.json` records their results and the source hash.

## Targets, in brief order

| Target | Checkpoint result | Proof route |
|---|---|---|
| `Turing.loop_run` | **Proved, no admission root** | Induction on the candidate count, with shifted configuration and acceptance families; compose rejected segments with `runFrom_add`. The existing exhaustion hypothesis handles zero candidates. |
| `Turing.FinTM.exists_loopCfgTM` | **Conditional; construction remains open** | Instantiate the concrete `loopHost` and generalized `loopHost_contracts` in fixed-verdict mode. The latter is the sole admitted construction frontier. |
| `Turing.FinTM.exists_loopTM` | **Conditional on the same frontier** | Apply the configuration export, the proved private `loop_halted_run`, then `ComputesInTime.mono` to absorb startup. No application of the incompatible frozen `loop_run` to a `[false]` terminal. |
| `Turing.FinTM.exists_loopFindTM` | **Conditional on the same frontier** | Instantiate the same host in payload mode and use the proved private `loop_find_run`. Its ordered-range induction and `List.find?_map` identify the first accepting payload. |

The targets were taken in the brief's order. After isolating the unfinished
second construction, the downstream corollary derivations were completed
conditionally; this does not count target 2, 3, or 4 as fully discharged.
There is one textual `sorry`, inside `loopHost_contracts`; there are no other
new admissions. `CONTINUATION.md` gives the exact declaration and remaining work.

## Audit construction ledger → implementation/proof status

| Round-3 ledger item | Checked material in this checkpoint | Still required inside `loopHost_contracts` |
|---|---|---|
| Finite controller phases | `LoopHostState`, `loopFuelSource`, `loopBodySource`, `loopControlAction`, and concrete `loopHost`; all definitions typecheck. The controller has separate fuel, startup-body, active-body, counter, and final phases. | Prove the complete phase assembly. A typechecked transition table alone is not its contract proof. |
| Fuel capture and genuine start | `loopHost_init` uses `initCfg_ofWords`; `loopHost_fuel_capture` instantiates W1 with the actual host; `loop_fuel_width` bounds bit width by the fuel budget. | Relate relocated source runs to `F`, then prove fuel capture rewind, copy/clear, and synchronized counter/capture rewind (phases 0–3). |
| Native input rewind | `loop_input_move_le`, `loop_input_run_le`, `loop_rewind_bounded`, and actual-host `loopHost_input_rewind` (phases 4–5). The bound uses the preceding run's displacement, not input length. | Connect that displacement estimate to the completed fuel setup in the startup sum. |
| Body startup and released first action | `loopBodyTM`/`loopBodyCfg`; `loopBody_stop`, `loopBody_step`, `loopBody_run`; `loopBody_capture` and actual-host `loopHost_body_capture`. The release bit forces a real source action before anchor recognition. | Lift the original seam and scratch-restoration hypotheses into the padded source; compose startup return/flag clearing and active-round returns. |
| Admissible orbit and configuration family | `loop_orbit_inv`; `loopDebit_iterate_length` and `loopDebit_iterate_value`. `loopFrame`, `loopWrite`, and `loopControl_apply` describe controller-local effects with arbitrary inactive residue. | Define the complete family of host seams, preserving fuel residue; establish startup equality and all empty-output clauses. |
| Accepting segment | `loop_first_halt` handles padded halting witnesses; body/capture lemmas preserve the halting emission; `loop_output_length_le` bounds payload length; `loopHost_replay` proves actual phase-13 replay in `payload.length + 1` steps. | Compose accepting return/flag recognition and the phase-12 rewind with final emission/replay and a uniform bound. |
| Rejecting segment before exhaustion | `loop_live_prefix`, `loop_silent_prefix`; standalone `loopBorrow_step`, `loopBorrow_run`, `loopBorrow_rewind`, `loopBorrow_correct`; exact debit arithmetic. | Lift the standalone debit into actual phases 8–9, prove flag clearing and equality to the next host seam. |
| Last rejecting segment and zero fuel | `loopDebit_success` identifies zero underflow; standalone decrement and rewind include empty width. Host phase 11 is the exhaustion dispatcher; initial release occurs before any debit. | Lift phases 8/10/11 and include underflow plus final emission in the last segment; choose and prove the halted terminal configuration. |
| Worst-case counter estimate | **Proved:** `2 * loopBorrowPos u + 2 ≤ 2 * u.length + 2`; width is preserved at every debit; fuel width is at most the actual fuel budget. No amortization is used for this estimate. | Transfer the same bound to the actual host, including its dispatch transitions. |
| Unreachable rejection terminal after acceptance | The proposed contract and controller permit the audit's arbitrary halted rejection terminal when the last candidate accepts. Local invariant lemmas apply to all orbit indices, including unreachable ones. | Implement the case split and prove the selected terminal and local contracts. |
| One constant ledger | Displacement, payload-length, counter-width, standalone counter-time, and actual replay bounds are proved. | Supply all remaining phase bounds and choose the single exported constant by the audit's maximum construction. **No completed uniform-constant proof is claimed.** |

The already-halted-terminal summation lemma is **`loop_halted_run`**. It is
admission-free, as is the first-payload summation lemma **`loop_find_run`**.
The corresponding summation proofs handle zero candidates; the host still
needs its construction proof for the separate zero-fuel/one-candidate case.

Harvests: the summation proofs adapt `ClassNP/EXP.lean`'s private
`enumLoop_run`; the fixed-width borrow privately adapts its `enumCarry*` and
buffer templates, reversing the bit roles for decrement. The bounded input
rewind follows `Simulation.lean`'s proved `rewind_from_any`/`rewind_scan` recipe,
retaining the exact time witness. No foreign private declaration is cited.
The body's stop-flag wrapper and concrete host are local constructions.

## Admissions and sanctioned W1 dependency

The kernel-environment traversal includes declaration types and values,
including opaque values, and follows constructor dependencies. It checks the
four targets and every one of the 55 new private declarations (59 checks).

- `loop_run`: no admission roots; only the standard axiom triple.
- All three public combinators: exactly `[Turing.FinTM.loopHost_contracts]`.
- `loopBody_capture`, `loopHost_body_capture`, `loopHost_fuel_capture`:
  exactly `[Turing.capture_run]`, the sanctioned W1 root.
- `loopHost_contracts`: its own direct admission root.
- All other new private declarations: no admission root.
- Every checked axiom list is a subset of the standard triple, with `sorryAx`
  present exactly for the declared roots above. No other axiom was found.

Thus W1 is used and root-verified in the capture helpers. It is currently
**unused in the public targets' proof dependency graph**, because the admitted
assembly has not yet consumed those helpers. Removing the assembly admission
must produce actual proof dependencies on the supporting lemmas; the present
root audit must not be misread as construction completion.

Headline prints from the fresh tree:

```text
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Verification

- Lean `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; committed manifest unchanged.
- `lake exe cache get` was invoked once. It failed during transfer; isolated
  cache recovery used the built cache executable to fetch 566 missing files.
  This setup failure was repaired before the successful sweeps. No `lake build`
  was invoked. `verification/environment.json` records this recovery explicitly.
- Bootstrap checked all modules in the committed order; subsequent iteration
  checks covered the owned module and the later 47-module suffix.
- **Final full fresh sweep:** all 57 modules, exact committed order, 57 fresh
  nonempty oleans, **zero `error:` lines**, exit 0. The tree was new and separate
  from the bootstrap/iteration output.
- Final sweep admissions: 48 declaration warnings = 4 Wrappers + 1 Loop +
  15 Primitives + 28 outside Build. The drop from the baseline's 51 is partly
  admission consolidation and is **not** evidence that three combinators closed.
- Lint: owned Build subtree **0 FAIL / 1 WARN** over 4 files. Full machine
  subtree **0 FAIL / 7 WARN** over 28 files; ClassNP **0 FAIL / 1 WARN** over
  10 files. Combined: 0 FAIL / 8 WARN over 38 distinct files. Seven are the
  inherited file-size warnings; the eighth is this owned file, addressed below.
- Freeze: five public signatures/order preserved, no public gains/losses,
  55 new private declarations, one source file changed, one textual admission.
- `git diff --check`, reverse patch application check, and `git bundle verify`
  all passed. The bundle advertises `fill/lib-L` and requires the recorded base.

Final sweep tail:

```text
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=135.9
```

## Shared lemmas and escalations

Requested shared lemmas: **none**. No frozen statement was judged false or
changed; no statement-level escalation is asserted.

**Size exception for maintainer review:** the owned file is 1,466 lines. The
brief's exclusive ownership prevents moving these helpers into another file
within this batch, and the shared controller, supporting simulation lemmas,
and exact continuation interface form one construction. The continuation is
kept together so another agent can complete the existing frontier without
reconstructing its machine. Lint therefore has one documented new WARN; this
is not a claim that a maintainer already approved the size exception.

## Complete new-private-declaration inventory

All line numbers below refer to the supplied `Build/Loop.lean`.

| Declaration | Kind | Line | Admission status |
|---|---|---:|---|
| `loop_live_prefix` | lemma | 172 | No admission |
| `loop_silent_prefix` | lemma | 183 | No admission |
| `loop_first_halt` | lemma | 197 | No admission |
| `loop_orbit_inv` | lemma | 220 | No admission |
| `loop_fuel_width` | lemma | 230 | No admission |
| `loop_input_move_le` | lemma | 237 | No admission |
| `loop_input_run_le` | lemma | 251 | No admission |
| `loop_output_length_le` | lemma | 267 | No admission |
| `loop_rewind_bounded` | lemma | 284 | No admission |
| `loopDebit` | def | 316 | No admission |
| `loopBorrowPos` | def | 322 | No admission |
| `loopBorrowPos_le` | lemma | 327 | No admission |
| `loopDebit_length` | lemma | 333 | No admission |
| `loopValue` | def | 339 | No admission |
| `loopValue_bits` | lemma | 344 | No admission |
| `loopDebit_value` | lemma | 355 | No admission |
| `loopDebit_success` | lemma | 369 | No admission |
| `loopDebit_iterate_length` | lemma | 380 | No admission |
| `loopDebit_iterate_value` | lemma | 390 | No admission |
| `loopBuffer_read` | lemma | 404 | No admission |
| `loopBuffer_write` | lemma | 412 | No admission |
| `loopDebitTM` | def | 433 | No admission |
| `loopDebitCfg` | def | 449 | No admission |
| `loopBorrow_step` | lemma | 456 | No admission |
| `loopBorrow_run` | lemma | 482 | No admission |
| `loopBorrow_rewind` | lemma | 507 | No admission |
| `loopBorrow_correct` | lemma | 541 | No admission |
| `loopBodyTM` | def | 559 | No admission |
| `loopBodyCfg` | def | 582 | No admission |
| `loopBody_stop` | lemma | 594 | No admission |
| `loopBody_step` | lemma | 612 | No admission |
| `loopBody_run` | lemma | 659 | No admission |
| `loopBody_capture` | lemma | 687 | W1 only |
| `LoopHostState` | abbrev | 710 | No admission |
| `loopFuelSource` | def | 714 | No admission |
| `loopBodySource` | def | 722 | No admission |
| `loopControlAction` | def | 729 | No admission |
| `loopHost` | def | 753 | No admission |
| `loopHost_body_capture` | lemma | 830 | W1 only |
| `loopHost_fuel_capture` | lemma | 844 | W1 only |
| `loopHost_init` | lemma | 856 | No admission |
| `loopControl_idle` | lemma | 865 | No admission |
| `loopHost_input_rewind` | lemma | 873 | No admission |
| `loopFrame` | def | 890 | No admission |
| `loopWrite` | def | 910 | No admission |
| `loopControl_apply` | lemma | 917 | No admission |
| `loopReplayTM` | def | 953 | No admission |
| `loopReplayCfg` | def | 963 | No admission |
| `loopReplay_step` | lemma | 969 | No admission |
| `loopReplay_run` | lemma | 993 | No admission |
| `loopControl_payload` | lemma | 1009 | No admission |
| `loopHost_replay` | lemma | 1029 | No admission |
| `loopHost_contracts` | lemma | 1083 | **OPEN construction** |
| `loop_halted_run` | lemma | 1217 | No admission |
| `loop_find_run` | lemma | 1351 | No admission |

## Delivery and integration

- Full source: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.
- One-commit `git format-patch` series: `patches/`.
- Delta bundle: `fill-lib-L.bundle`, requiring base `e346139ccc9e3141908f7414bf27f74d8759c9be`.
- Continuation instructions and exact admitted declaration: `CONTINUATION.md`.
- Required logs: `logs/final-sweep.log`, `logs/axioms.log`; lint, freeze, and
  bundle verification logs are included too.
- Reproducible audit programs and machine-readable summaries: `verification/`.
- Checksums: `SHA256SUMS`, covering every other file in the archive.

Apply the patch with `git am -3` on a checkout descended from the required
campaign branch, preserving unrelated concurrent W/P work. Treat this as a
checkpoint, not an acceptance-ready fill. Recheck the frozen statements and
rerun the committed 57-module sweep and axiom traversal after integration.
