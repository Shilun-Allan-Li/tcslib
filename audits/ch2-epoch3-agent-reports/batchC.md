# Chapter 2, epoch 3, batch C — complete

All five assigned lemmas are proved. `Snapshot.lean` is admission-free. No frontier, partial target, escalation, or requested shared lemma remains.

## Provenance and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required base: `b55180a8bb38b94427e75e63630aa6eab5fd6e95`.
- Working branch: `fill/ch2-e3-C`.
- Delivery commit: `771630afa6270b21c23728a592ee898d02d6419c`.
- Governing brief: committed `briefs/ch2-epoch3-batchC.md` on `complexity/arora-barak-ch1`; its required base was honored exactly. The brief was checked against the live GitHub file (blob `235eee33d1f0da08cc0358ca3d6e9157708c961c`).
- Only changed tracked path: `TCSlib/Complexity/CookLevin/Snapshot.lean`.
- No rebase, remote write, push, or PR. The base branch was not modified.
- Final source: **368 lines, 18,606 bytes**; net diff **121 insertions, 5 deletions**.
- Source SHA-256: `d30d4ef5746e14dd011e038906baed120b1dcd71f5bd6e8f2e6ef8bf3ef8bc77`.

The report, verification programs, logs, and delivery files live outside the repository, so they do not enter the source patch.

## Targets and kernel dependencies

Every target below is in namespace `Complexity`; every admission-root list is empty. Axiom names are printed literally in `final-axioms.log`.

| Target | Status | Axioms |
|---|---|---|
| `oblivious_schedule_eq` | Proved | `propext`, `Quot.sound` |
| `snapshotAt_zero` | Proved | `propext`, `Classical.choice`, `Quot.sound` |
| `snapshotAt_state_succ` | Proved | `propext`, `Quot.sound` |
| `snapshotAt_inputSymbol` | Proved | `propext`, `Classical.choice`, `Quot.sound` |
| `snapshotAt_workSymbol` | Proved | `propext`, `Classical.choice`, `Quot.sound` |

No `sorryAx`, sanctioned admitted dependency, new axiom, unsafe declaration, or `native_decide` is used. The final kernel traversal follows declaration types, values including opaque proofs, and inductive constructors, using the committed epoch-2 closure-audit template. It also confirms that all four new private helpers occur in the final work-symbol theorem's dependency closure and checks their roots and axioms separately.

## Complete new-declaration inventory

Exactly four source declarations were added, all `private lemma` in `Complexity`:

| Helper | Role |
|---|---|
| `workCell_succ` | Exact old-head cell recurrence for one step. |
| `workCell_eq_of_no_visit` | A fixed cell's content is constant over an interval without a visit. |
| `prevVisit_none_no_visit` | An absent filtered maximum excludes every strictly earlier visit. |
| `prevVisit_some_last` | Membership and maximality give the strict earlier-time bound, matching position, and absence of intervening visits. |

No public declaration was added, removed, renamed, reordered, or re-signatured. No existing definition, import, option, or docstring changed. The only added documentation is the four new private-helper docstrings and two inline proof comments; **no append to an existing docstring** was needed. Nontrivial helpers carry adjacent proof sketches.

## Derivation-A discharge map

| Audited obligation | Discharge |
|---|---|
| Cell recurrence (1) | `workCell_succ`, after `runFrom_succ_eq_step'`, splits on the source state and uses public `Turing.Action.apply_workTapes` plus `Function.update_apply`. The test compares the queried cell with the **old** head position. |
| Optional writes: outer `none` versus `some none` | `Action.apply_workTapes` preserves the original nested optional write with `getD`: outer `none` retains the scanned value; `some none` yields blank. `workCell_succ` consumes that exact public identity without flattening either option. |
| Halting-transition write, including simultaneous movement | The live branch of `workCell_succ` applies the action without any condition on its successor state or movement. Consequently the write at the old head is retained even when the action halts. |
| Absorbing halted source | The `none` source-state branch of `workCell_succ` uses the unchanged configuration returned by `step`; `writtenOrKept` is the old scanned value. All later interval arguments apply unchanged. |
| Schedule transport | `oblivious_schedule_eq` instantiates obliviousness on the actual input and the all-false input of equal length. Local fact `hp` in `snapshotAt_workSymbol` specializes work-position function equality at the chosen tape. |
| Strict earlier-time bound | `prevVisit_some_last` obtains `s < t` from membership in `List.range t`. The absent-visit helper uses the identical strict bound. Neither proof includes the current time in the filtered list. |
| `prevVisit = none` | `prevVisit_none_no_visit` turns the absent maximum into an empty filtered list. The final theorem transports this to actual positions and applies `workCell_eq_of_no_visit` from time zero to the current time; the initial cell is definitionally blank. This includes time zero. |
| `prevVisit = some s` | `prevVisit_some_last` gives the position equality and maximality. `workCell_eq_of_no_visit` runs from `s + 1` to the current time; `workCell_succ` supplies the value written or retained by step `s`. The interval can be empty, so consecutive visits are covered. |
| Empty input and zero work tapes | No positivity hypothesis was introduced. `FinTM.inputSymbol_at` handles the empty-input right boundary; work-symbol statements quantify over an arbitrary existing tape index. |

The proof uses the public run-calculus and simulation identities already available through the frozen imports. It introduces no machines, clocks, budgets, or common-halting-time assumption.

## Verification

1. **Pinned environment:** Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
2. **Setup:** `lake exe cache get` was attempted once. Its upstream ProofWidgets release step failed; `lake exe cache unpack` restored 7,506 matching cached files successfully. Both setup logs are included. No TCSlib `lake build` was invoked. All TCSlib elaboration ran through the prescribed direct-Lean script.
3. **Container compatibility:** the stock Lean executable needed a process-path workaround: its own `/proc/<pid>/exe` lookup was redirected to `/proc/self/exe`. The included `proc-self.c` records the entire shim; Lean source, binary, and kernel were unchanged. Ordinary environments do not need it.
4. **Bootstrap and iteration:** all 57 ordered modules passed the bootstrap; the owned module was checked incrementally while filling the five targets and four helpers.
5. **Final fresh sweep:** a separate, initially empty `.lake/final-oleans` tree; all 57 modules in `scripts/ab_ch1_module_order.txt`, each through `scripts/lean_check_tree.sh`. **57 exit-zero checks, zero `error:` diagnostics, a fresh olean per module.** The final sweep retains 16 pre-existing out-of-scope admission warnings, with none in `Snapshot.lean`.
6. **Final axiom audit:** `ClosureAxioms.lean` against the final fresh olean tree; all five public targets and four private helpers pass. The complete output is `final-axioms.log`.
7. **Freeze:** removing the exact four new private declarations and their documentation, then restoring only the five proof bodies, reproduces the entire base file **byte-for-byte**. This checks all frozen definitions, statements, comments, imports, options, and declaration ordering. Exactly five admission sites were removed. See `freeze.log`.
8. **Style and hygiene:** `git diff --check` passed. The committed style linter on `TCSlib/Complexity/CookLevin` reported **0 FAIL, 0 WARN** over its two files. The working tree is clean.
9. **Transport:** bundle verification passed. Applying the patch to an isolated index at the required base reproduced the exact delivery tree `ddc503fd2a330a4e9b5b158620043551567fccc4`; no additional branch was touched.

Final sweep tail:

```text
[55/57] TCSlib/Complexity/Formulas
SOURCE_SHA256 d85932e65718ca00656ae679513006890abf6cae2c84bbf15002496e1c53f5a3
EXIT 0; elapsed 1.34s
[56/57] TCSlib/Complexity/CookLevin
SOURCE_SHA256 1867b5b18261f0508f4e8c33e7364779027970fd0eb709fab650bd6cb4c6f2ca
EXIT 0; elapsed 1.22s
[57/57] TCSlib/Complexity/ClassNP
SOURCE_SHA256 5a48034d29c5a6feea0a3b249531cbd6bed499cc5bbce88ba000f5d1cf26b904
EXIT 0; elapsed 1.21s
SWEEP_COMPLETE 57 modules; zero error diagnostics
```

## Delivery and integration

`fill-ch2-e3-C.zip` is flat: every member, including `SHA256SUMS`, is at the root. `SHA256SUMS` covers every other member. The full source member `Snapshot.lean` maps to `TCSlib/Complexity/CookLevin/Snapshot.lean`. The single format-patch file and incremental git bundle encode the same commit; the bundle requires the base commit recorded above.

After extracting, verify `sha256sum -c SHA256SUMS`. Apply the single `0001-*.patch` with `git am -3` in the maintainer's intended integration checkout, or inspect the bundle. To reproduce the checks, bootstrap the prescribed module order with `scripts/lean_check_tree.sh`, then run `ClosureAxioms.lean` with that fresh olean tree and the pinned package paths on `LEAN_PATH`.

**Requested shared lemmas:** none. **Escalations:** none. **Remaining assigned admissions/frontier:** none.
