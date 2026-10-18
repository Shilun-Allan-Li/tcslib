# Machine-routine layer (§12): statement-gate audit

**Verdict: FAIL — 0 blockers, 4 majors, 3 minors, 3 notes.** The gate remains open. I found no counterexample to the mathematical conclusions of the 47 sorried declarations. The majors concern missing interfaces for named consumers and a materially incorrect witness/space argument; they are not claims that all four affected existential statements are false.

Audited source: the attached bundle at commit `7fbac9bdff79aee148b916e077ad93b6ce4693f9`, branch `complexity/arora-barak-ch3-4`. Audit date: 2026-10-09 UTC. Bundle SHA-256 independently computed and matched:

```
e9216b8b59eeb749484ba6f3f956ced25e7a55fe900c859924a0339e5bef4673
```

Scope: `Build/Embed.lean`, `Build/Seam.lean`, and `Build/Catalog.lean`, including concrete definitions, statement shapes, and sketches. Paths and line numbers below refer to the extracted attachments, not the combined bundle. Frozen files were read as evidence and were not modified. This is a statement audit, not a fill audit or a kernel-checked proof of the new statements.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R1 | major | `Embed.lean:187,198` · `embedSilentTM`, `embedEmitTM`; module design paragraph | Preserving the source halt does not leave live-return dispatch to the current seam combinator successfully. The claimed replacement of returning subroutine embeddings is incomplete. | A one-state source emits one bit and halts on its first transition. Its closed embedding reaches `state = none`; every subsequent composite step remains halted. Choosing its sole live state as `seamCompTM`'s exit instead dispatches **before** that transition and loses the emission. `Wrappers.captureAction`/`emitAction` and `Primitives.emitterRightTM` explicitly perform the missing halt-to-live transition. See the formal trace below. | Keep the closed transformers, but add an arbitrary-bank, host-parametric returning action/configuration/run interface, or a named halt-to-live adapter with an exact through-halt contract. Preserve the final emission and arbitrary source tape residue. Do not claim that `seamCompTM` alone supplies this operation. |
| R2 | major | `Seam.lean:136–212` · `seamCompTM_run`, `_firstReturn`, `_visitedByTapeHead`; R1-to-R2 consumer claim | Canonical-only composition cannot consume the arbitrary frames and output configurations promised by R1 and used by the retrofit. | All three seam configurations force input head `1`, all work heads `0`, canonical contiguous words, and empty output. An embedded source can return while an inactive host head remains at `7`, or with forwarded output `[true]`; neither configuration equals any `Cfg.ofWords`. Attached `emitterP2_relocate_run` accepts arbitrary frames/configurations; `emitterBank_clear` retains an arbitrary input position; `exists_emitCallTM` explicitly returns a seam **with nonempty output**. The current machine definition could sequence these, but the exported theorems cannot certify them. | Export a general-configuration composition theorem, with phase two starting from phase one's returned configuration after replacing its control state. Preserve heads, tapes, input position, and accumulated output across dispatch. Derive the canonical theorem and visited-set corollaries from it. |
| R3 | major | `Seam.lean:136,164` · `seamCompTM_run`, `seamCompTM_firstReturn` | The interface does not cover positive calls whose entry equals exit, so its chaining claim does not cover the attached clean-call interfaces. | For `start = exit` and `T₁ > 0`, `hcut` at `t = 0` is contradictory. Operationally the composite dispatches immediately. For `entry = q₂` and `T₂ > 0`, `_run` may apply, but `_firstReturn`'s `hcut₂` is contradictory at zero. `exists_installCallTM` and `exists_emitCallTM` promise only **strictly positive** interior exclusion and do not promise distinct entry/exit; `emitterP2_call_segment` explicitly executes the first source action before testing return. | Add a fresh-entry/release adapter that executes the entry action unconditionally, then tests the exit. Export its positive-first-return theorem and the corresponding composition/space result. Merely removing zero from `hcut` while retaining the current transition table would make the theorem false. |
| R4 | major | `Catalog.lean:831` · `computesFunInTime_pairMapSnd_spaceUsed`, sketch at 817–830 | The new space conclusion is plausible, but the asserted annotation of the existing captured-payload witness is not witness-honest. | The original witness is `pairMapTM (bufferedCompTM (pairExtractTM false true) Mg)` (`Primitives:2747`). `pairMapTM` captures **all** of `g b`, so its capture head visits at least `\|g b\| + 1` cells. Take the existing unary-square generator: `g b = replicate ((\|b\|+1)^2) true`, with `Sg(n) = O(n)`. On `pairEncode [] b`, the new bound is `O(\|b\|+1)` but this witness visits quadratically many cells. Output length is not bounded by the payload's visited-work-space hypothesis. | Either retain the captured witness and add an output-length/time term, or explicitly commission a different controller: validate/buffer the input pair, emit its encoded first component, then simulate `Mg` on the buffered second component **forwarding** its output. The latter supports the current conclusion with unchanged coefficient `1` on `Sg`. Name these construction obligations in the sketch and brief. |
| R5 | minor | `Catalog.lean:651` · `computesFunInTime_polyBits_spaceUsed` | The stated bound needs a special witness choice when `C = 0`; the unqualified buffered-generator proof route fails there. | For `C = 0`, the bound is constant `c`. For `e > 0`, the original `catalogPolyUnaryTM (e-1) 0` still initializes unary work banks of length `n+1`, and buffered composition retains those banks. Thus its visited space is unbounded in `n`, despite empty output. The existential theorem remains true using the existing constant-empty-output family. | Explicitly split `C = 0`, using a constant witness; split `e = 0` as the fixed-value case. Use buffered unary generation only when `C > 0` and `e > 0`, where `n+1 ≤ C(n+1)^e`. |
| R6 | minor | `Catalog.lean:437–445` · `compareTM_spaceUsedByTape` sketch | The stated visited bound is correct, but the supplied interval/cardinality argument is not. | The integer interval `[-1, min+1]` has `min+3` cells. A conditional observation about mismatches does not cover equal inputs. Direct transition counting gives the stronger trajectory `[-1,d]`, where `d ≤ min` is the first mismatch or terminating-blank position, hence `d+2 ≤ min+2` cells in every case. | Replace the sketch by the exact position/count argument below, uniformly including equal words, unequal lengths, and aliased tape indices. |
| R7 | minor | `Catalog.lean:461–471` · `incrementTM_run_succ` sketch | The success sketch mixes two different counts and describes a head position not attained by the machine. | If the first `false` is at position `p`, the machine takes `p` carry steps, one left-turn/write step, `p` rewind steps, and one right-entry step: exactly `2p+2`, not that count plus two further boundary steps. It never moves right to `p+1` on success. Input `[false]` returns in two steps. | State exactly `2p+2 ≤ 2\|w\|`, with visited interval `[-1,p]`; retain the looser public bound `2\|w\|+2` if desired. |
| R8 | note | `Catalog.lean:777–786` · `computesFunInTime_stripLast_spaceUsed` sketch | The space bound is honest, but the explanation that quadratic time “comes from replays” misdescribes the attached witness. | `rawStrip_computes` gives `4(n+1)`, and the actual guard/composition/conditional proof derives a linear bound before weakening it to `(n+1)^2`. The raw buffer and guard buffers are linear; no quadratic-size storage is needed. | Describe the quadratic contract as deliberate slack and account for both guard and raw-strip banks. |
| R9 | note | Design §12 consumer table; `Embed.lean` consumer claim | Physical-tape selection is not a theorem about several zones on one tape or a complete `k`-to-2 simulation. | `ι : Fin m ↪ Fin k` selects whole distinct tapes and preserves integer coordinates. It cannot instantiate `Fin 3 ↪ Fin 2`, alias two virtual tapes to different regions of one physical tape, or change the source input word. | State which fixed physical-tape routines the Hennie–Stearns and universal-machine constructions will use. Supply their spatial/virtual-input encoding interfaces separately; do not infer full consumer adequacy from R1 alone. |
| R10 | note | `Catalog.lean:920–940` · L-row scope; decision 12.3 | The decision-loop bound is sound, but its existential conclusion does not export the claimed same-host space facts for the configuration and result-bearing siblings. | `exists_loopTM_spaceUsed` exports only a Boolean function machine. The attached `exists_loopCfgTM` and `exists_loopFindTM` expose additional configuration/payload behavior that cannot be recovered from that conclusion. A promise that they inherit the host “at fill time” is not a frozen statement. | Before a consumer needs those behaviors with space, add same-witness conjunctions for the sibling contracts, or a shared named-host contract. This is not a refutation of the audited decision row. |

## Integrity, coverage, and evidence limits

| Item | Independently checked result |
|---|---|
| Concrete definitions | 12 `def` declarations, including two private helpers, plus two inductive phase types: all 14 restated below. Derived equality/finite instances follow from those finite types. |
| Sorried statements | Exactly 47: Embed 9, Seam 6, Catalog 32. Every declaration is covered below. |
| New axioms | No `axiom` declarations in the three files after stripping comments. |
| Frozen attached Build files | `Convention`, `Wrappers`, `Loop`, and `Primitives` contain no uncommented `sorry` or `axiom` declarations. |
| Attached elaboration log | Exactly 47 `declaration uses 'sorry'` warnings, matching declaration names and source lines; zero `error:` lines; correct full commit in the header. |
| Attached style log | Reports 0 FAIL, 8 pre-existing size WARNs, none on an audited file; Catalog has a non-failing target-size INFO. |
| Part-2 restatements | 19/19 existential time clauses match; all inherited parameters/hypotheses match after deleting only the declared added space parameters/hypotheses. W1 and W2 were compared separately. |
| Finite execution diagnostic | 16,764 cases passed, covering all binary words of lengths 0–6, all ordered word pairs for compare, self-compare, nonempty frame tapes, exact completion times, returned tape contents, exact visited sets, and five further stationary steps. This diagnostic is not a proof for arbitrary length; the symbolic derivation follows. |

A fresh Lean build was **not** run: the packet is not a complete checkout/toolchain, and `lean` is unavailable in this workspace. The log supports the reported elaboration outcome, but does not independently establish fresh `.olean` timestamps or reproduce the build. Likewise, one supplied copy of each frozen file cannot prove byte identity with an earlier audited revision; no second baseline was attached. No repository mutation or GitHub write was performed.

`[Bon26]` is present in all three module reference sections, at the adapted principal definitions, and at the main adapted lockstep/composition/run declarations. The live [Lax archive entry](https://laxarchive.org/lax-434930/) independently confirms the author, archive identity, Lean 4.33 epoch, and linked `0c0840319318215fd7b36a9a822b81ce55cf6941` revision. Retrieval of the pinned GitHub files and license was blocked, so the exact `StackRename`/`StackProgram` declaration names and Apache-2.0 license were **not independently verified**. Blueprint files were not attached; their citation compliance is unchecked. These limits do not affect the local transition counts or contract diffs.

The sharp-space witness behind `Complexity.timeConstructible_id`, used by the original `computesFunInTime_lengthBits`, is also outside the attachment set. The new logarithmic-space theorem has a direct construction argument below; the claim that this is literally a space annotation of that imported witness remains unverified.

## Blind restatements of definitions, then comparison

These are declaration-based restatements: the bodies determine the meaning; the prose is then compared against that meaning. `Cfg.ofWords` in the frozen context has input position **1**, all work heads **0**, one contiguous word per tape starting at 0, live control, and empty output. Work-space counts positions at times **0 through t inclusive**, including an initially stationary head's cell.

| Definition | Restatement from the body | Comparison |
|---|---|---|
| `embedSlot` (private) | Search all source indices in finite order for the unique index mapped to host index `j`; return `none` if there is none. | Accurate. Injectivity makes the first successful search result the only result. |
| `embedActionCore` (private) | Preserve input motion and successor state. Selected host tapes receive the corresponding source action; other tapes are stationary except an off-bank capture tape, which writes and advances on emission. With no sink, forward the emission; with a sink, suppress physical output. | Accurate. Selection takes precedence over the sink, so a sink on the selected bank does not capture; the public silent contracts exclude this. |
| `embedSilentCfg` | Preserve source state/input position; put source contents and heads on selected tapes. On an off-bank capture tape put `pre ++ c.output` with head at its length, retain ambient contents/heads elsewhere, and set physical output to `out₀`. | Accurate under `hcap`; it preserves a halted state rather than creating a live return. The docstring's “`m = k`-with-last-tape-selection” is imprecise: the capture specialization is a source of `m` tapes in a host of `m+1`. |
| `embedEmitCfg` | Preserve source state/input position; relocate selected contents/heads, retain every other frame tape/head, and set output to `pre ++ c.output`. | Accurate. Identity tape selection gives forwarding without tape relocation; state behavior still differs from returning `emitCfg` at halt. |
| `embedSilentTM` | Use the source start state and state type; read source work symbols from the selected host tapes, then apply the suppressing core. | Accurate as a closed transformer; consumer-return claims have R1. |
| `embedEmitTM` | Same selected-symbol simulation, forwarding emissions and preserving the source state type and halt. | Accurate as a closed transformer; it changes neither the input word nor tape coordinates. |
| `seamCompTM` | On left states, simulate the first table except that `exit` immediately makes one stationary silent transition to the chosen right entry. On right states, simulate the second table. Either source halt remains an actual halt. | Accurate. Dispatch happens before any transition of the left exit state; there is no first-call/release bit. |
| `SweepPhase` | Three controls: `sweep`, `rewind`, `done`. | Accurate. `done` is live and stationary in the three consuming routines. |
| `FlagPhase` | Five controls: `run`, two Boolean-labelled `rewind` controls, and two Boolean-labelled `done` controls. | Accurate; the Boolean verdict is in the live control, not the output tape. |
| `transferTM` | Scan the source right while writing the same bits on the destination; at the first source blank turn left; erase source cells while returning; on the left blank move right and enter stationary `done`. | Correct from canonical words with distinct indices and blank destination. The definition exists for equal indices, but the contracts correctly exclude that case. |
| `copyTM` | The same scan and rewind, without source erasure. | Correct under its stated distinct-index/blank-destination hypotheses. |
| `clearTM` | Scan the intact target word to its right blank, turn left, erase all word cells while returning, and step right from the left blank to stationary `done`. | Accurate. The left blank is detected before an erased region can be mistaken for it, because erasure proceeds behind the returning head. |
| `compareTM` | Advance both selected heads once on equal nonblank symbols. At a differing pair or a single blank turn left carrying `false`; at a double blank turn left carrying `true`. Rewind using the unchanged first tape, then step right from the left blank. | Correct also when indices coincide: the disjunction selects one action per physical tape, not two sequential moves. |
| `incrementTM` | Change the initial run of `true` bits to `false` while moving right. At the first `false`, write `true` and turn left with success; at a blank turn left with overflow. Return over the still-nonblank prefix and enter the corresponding stationary exit. | Exactly fixed-width little-endian increment; overflow leaves the original width filled with `false`, including width zero. |

## Independent movement counts and space intervals

Here `L` is the touched word's length. For compare, `d` is the first unequal-symbol position, or the first position where at least one word ends; thus `d ≤ min(|u|,|v|)`. For increment success, `p` is the first `false` position, so `p < L`.

| Routine/case | Forward moves | Turn transition | Return moves over cells | Final right-entry transition | Exact first exit time | Exact final touched-tape visited set |
|---|---:|---:|---:|---:|---:|---|
| transfer | `L` | `1` | `L` | `1` | `2L+2 ≤ 3L+3` | integers `[-1,L]`, size `L+2`, on both tapes |
| copy | `L` | `1` | `L` | `1` | `2L+2 ≤ 3L+3` | integers `[-1,L]`, size `L+2`, on both tapes |
| clear | `L` | `1` | `L` | `1` | `2L+2` | integers `[-1,L]`, size `L+2` |
| compare | `d` | `1` | `d` | `1` | `2d+2 ≤ 2 min(\|u\|,\|v\|)+2` | integers `[-1,d]`, size `d+2` |
| increment, success | `p` | `1` | `p` | `1` | `2p+2 ≤ 2L` | integers `[-1,p]`, size `p+2` |
| increment, overflow | `L` | `1` | `L` | `1` | `2L+2` | integers `[-1,L]`, size `L+2` |

The counts can be checked by the following invariants, including the boundary steps:

1. **Transfer/copy/clear.** After `r ≤ L` forward transitions the active heads are at `r`, control is `sweep`, and the source word is intact; the destination, when present, contains exactly the first `r` bits. The turn reads the blank at `L` and moves to `L-1`, taking time `L+1`. After a further `r ≤ L` rewind transitions the heads are at `L-r-1`, with exactly the last `r` source cells erased in transfer/clear. At time `2L+1` the heads are at `-1`; the next transition enters `done` at 0. Thus
   \[
   T=L+1+L+1=2L+2,\qquad |[-1,L]\cap\mathbb Z|=L+2.
   \]
   All other tapes receive `(none,0)` at every step. Both empty-word turns remain present, so `L=0` gives `0,-1,0`, not a zero-step return.

2. **Compare.** Every position strictly below `d` contains two equal nonblank bits. The turn at position `d` moves directly to `d-1`, never to `d+1`; all first-tape cells from `d-1` down to 0 are nonblank, even when the first tape is the shorter one. It therefore reaches `-1` after exactly `d` rewind moves and returns to 0 in one more step:
   \[
   T=d+1+d+1=2d+2,\qquad |[-1,d]\cap\mathbb Z|=d+2\le\min(|u|,|v|)+2.
   \]
   At `d=min`, simultaneous blanks mean equal words; one blank means unequal lengths. A mismatch before `min` means unequal words. These exhaust the cases and prove the verdict, including equal-prefix unequal-length inputs in both orientations.

3. **Increment.** If `w = replicate p true ++ false :: rest`, the first `p` transitions replace that prefix by `false`s; the next writes the successor's `true` at `p` and moves left. The preceding cells remain nonblank, so `p` left moves and one final right move restore the head. The resulting word is `replicate p false ++ true :: rest`, precisely the recursion defining `incFixed`; total `p+1+p+1=2p+2`. If no `false` exists, the same argument uses the right blank at `L` and leaves `replicate L false`, with total `2L+2`.

4. **All horizons.** Each `done` transition is stationary, write-free, silent, and stays in the same live state. Before completion the visited set is a subset of the interval above; afterwards it is exactly that interval. This proves the advertised bounds for **every** `t`, rather than only at a selected completion time. Untouched tapes have visited set `{0}` and cardinality 1, even when their initial word is nonempty.

5. **Embedding/capture constants.** Selected heads agree pointwise with the source heads; unselected fixed heads have singleton visited sets. An off-bank capture head begins at `|pre|+|c.output|` and advances by 0 or 1 according to whether the source emits. Therefore its exact visited cardinality is
   \[
   |(M.runFrom\ c\ t).output|-|c.output|+1.
   \]
   Append-only output makes the subtraction nonnegative, so Lean's natural subtraction is safe. Large pre-existing prefixes are not counted as visited in this new run window; that is the declared visited-head measure, not a bound on preloaded nonblank storage.

6. **Seam dispatch constant.** Phase-one lockstep gives the left exit configuration at `T₁`. Exactly one transition changes only control to the right entry, and phase-two lockstep then gives the claimed result at `T₁+1+T₂`. The dispatch visits no additional position: its position is already the first phase's final position and the second phase's initial position. This proves the stated union containment, in fact equality, over that finite horizon.

## All 47 sorried statements: restatement and validity argument

“Supported” here means a mathematical statement-level argument from the supplied definitions; filling the Lean proof remains required. The major interface findings remain applicable even where a theorem is true under its hypotheses.

### Embed: 9/9

| Declaration | Restatement and argument |
|---|---|
| `embedSilentTM_runFrom` | **Supported.** For any source configuration, frame, output prefixes, and time, off-bank capture commutes with running for exactly that time. At a live step the selected reads/actions agree and an optional output is appended at the capture head; at halt both machines stutter, so induction has no liveness guard. |
| `embedSilentTM_frame` | **Supported.** Every unselected non-capture tape retains its whole ambient function and head, the input head equals the source's, and physical output remains `out₀`. These are componentwise projections of the preceding lockstep identity. |
| `embedSilentTM_visitedByTapeHead` | **Supported.** A selected host tape has exactly the source tape's visited set and its cardinality at every horizon. Apply the lockstep identity at each time in `range (t+1)` and take image equality, then cardinality. |
| `embedSilentTM_visitedByTapeHead_frame` | **Supported.** An unselected non-capture tape visits precisely its initial head singleton and uses one cell. The frame result makes the trajectory constant, and `range (t+1)` is nonempty even at zero. |
| `embedSilentTM_spaceUsedByTape_cap` | **Supported.** Capture uses at most output growth plus one visited cell, independently of the initial prefix length. The monotone unit-step capture trajectory proves equality with that expression, so the stated inequality is conservative. |
| `embedEmitTM_runFrom` | **Supported.** Forwarding commutes with every source run step, preserving the host output prefix before the source output. Associativity of list append handles emission, and preserved halts handle all post-halt times. |
| `embedEmitTM_frame` | **Supported.** Off-bank tapes and heads remain the ambient frame, input follows the source, and output is `pre ++ source.output`. These follow directly from the forwarding configuration and lockstep equation. |
| `embedEmitTM_visitedByTapeHead` | **Supported.** Selected host/source visited sets and per-tape counts coincide. Their head trajectories coincide at every sampled time, including zero and post-halt times. |
| `embedEmitTM_visitedByTapeHead_frame` | **Supported.** Every unselected head visits its initial singleton and uses one cell. No state, emission, or input-head behavior changes the stationary off-bank work action. |

### Seam: 6/6

| Declaration | Restatement and argument |
|---|---|
| `seamCompTM_run` | **Supported.** Given two exact canonical endpoints and no earlier first-phase exit, running the composite for `T₁+1+T₂` yields the mapped second endpoint. The first cut justifies every simulated left transition, one dispatch preserves the seam data, and right simulation has no exit override. |
| `seamCompTM_firstReturn` | **Supported, with R3 on scope.** If phase two also excludes its final anchor at every time below `T₂`, the composite excludes its final right anchor below the total time. Before dispatch all states are left states; after dispatch right-state injectivity reduces the claim to the second cut. |
| `seamCompTM_visitedByTapeHead` | **Supported.** Up to the stated total horizon, each composite visited set is contained in the union of the phase sets. Splitting the timeline at dispatch gives exactly the two trajectories; the repeated seam origin adds nothing. |
| `seamCompTM_spaceUsedByTape_le_add` | **Supported.** Each composite per-tape count is bounded by the sum of the two phase counts. Take cardinalities of the union containment and use the finite-set union inequality. |
| `seamCompTM_spaceUsed_le_add` | **Supported.** Total space over that horizon is at most the sum of phase total spaces. Sum the preceding per-tape inequality over the common finite tape index set. |
| `seamCompTM_spaceUsedByTape_le_max` | **Supported.** If either phase visits only `{0}` on the chosen tape, its composite count is at most the larger phase count. Both phase trajectories include 0 at their canonical initial configuration, so the singleton contributes no additional member to the union. |

### Catalog Part 1: 11/11

| Declaration | Restatement and argument |
|---|---|
| `transferTM_run` | **Supported.** For distinct source/destination and initially blank destination, a first exit within `3\|w src\|+3` leaves the source blank, the destination equal to the old source word, and the other seam fields intact. The sweep/erase invariant above gives the stronger exact first exit `2\|w src\|+2`, with `done` absent beforehand. |
| `transferTM_spaceUsedByTape` | **Supported.** At every time the two active tapes use at most `\|w src\|+2` cells and every other tape uses exactly one. The active trajectories are prefixes of `0→\|w src\|→-1→0` followed by stationary control; the frame actions are always stationary. |
| `copyTM_run` | **Supported.** Under the same index and blank-destination conditions, both source and destination contain the source word at first exit within `3\|w src\|+3`. No transition changes the source, and the destination's forward prefix invariant becomes the full word before rewind. |
| `copyTM_spaceUsedByTape` | **Supported.** Both active tapes have the transfer routine's space bound and the rest remain singletons. Removing erasure does not change any head movement. |
| `clearTM_run` | **Supported.** From any canonical word on the selected tape, first exit occurs within `2\|w i\|+2` with that tape blank and the rest preserved. The exact sweep/erase count equals the public budget. |
| `clearTM_spaceUsedByTape` | **Supported.** The selected tape uses at most its word length plus two cells at every horizon; each other tape uses one. Rewinding visits both boundary cells and stationary `done` prevents subsequent growth. |
| `compareTM_run` | **Supported.** A first visit to either exit occurs within twice the shorter length plus two, with verdict equal to list equality and every tape restored. The mismatch-position derivation proves the result in both unequal-length orientations and for aliased indices. |
| `compareTM_spaceUsedByTape` | **Supported; sketch repair R6.** Both compared tapes use at most shorter length plus two cells, with all others fixed. The actual interval is `[-1,d]` with `d≤min`, not the larger interval used in the sketch. |
| `incrementTM_run_succ` | **Supported; sketch repair R7.** If `incFixed (w i)=some v`, the first exit carries `true` and the selected tape contains `v`, within `2\|w i\|+2`. The first-false decomposition gives the exact output and first-exit time `2p+2`. |
| `incrementTM_run_overflow` | **Supported.** If `incFixed` returns `none`, first exit carries `false` and the word is replaced by a same-length all-false word. Structural recursion of `incFixed` makes this precisely the all-true case, whose scan/rewind time is `2\|w i\|+2`, including width zero. |
| `incrementTM_spaceUsedByTape` | **Supported.** The selected tape uses at most its original length plus two cells at every horizon; all other tapes use one. Success visits `[-1,p]`, overflow visits `[-1,L]`, and both final controls are stationary. |

### Catalog Part 2: 21/21

For the existential rows, the time clause and new space clause concern **one machine and one constant chosen before all inputs and times**. This quantifier shape is correct. It does not, by itself, assert equality with the old theorem's hidden existential witness; the separate witness-family check matters precisely for that reason.

| Declaration | Restatement and argument |
|---|---|
| `capture_visitedByTapeHead` (W1) | **Supported.** Under exactly the source-table agreement and pre-endpoint liveness conditions of `capture_run`, source-bank visited sets/counts agree and capture space is bounded by source output growth plus one. Apply `capture_run` at every prefix up to the supplied horizon; its liveness condition restricts to each such prefix. The final halting emission is included, while no claim is made about later host-return behavior. |
| `computesFunInTime_id_spaceUsed` | **Supported, same witness family.** Identity has linear time and a constant whole-run work-space bound, with the same existential machine in both clauses. The original `idTM` has zero work tapes, hence space exactly zero at all times. |
| `computesFunInTime_const_spaceUsed` | **Supported, same witness family.** A fixed output word has linear-in-input time allowance and constant work space. The original zero-work-tape finite emission chain satisfies both, with the constant chosen after the fixed word. |
| `computesFunInTime_prepend_spaceUsed` | **Supported, same witness family.** Prepending the fixed word has linear time and constant whole-run work space. The actual `catalogPrefixTM` has zero work tapes, a stronger property than the sketch's no-work-head-movement claim. |
| `computesFunInTime_lengthBits_spaceUsed` | **Supported by a direct construction; original witness's sharp space unchecked.** The machine must output binary input length in linear time using `O(Nat.size n+1)` visited cells. A variable-width binary counter can return its head after each carry and advance the input once per increment; the sum of carry lengths is bounded by `∑_{j≥1} floor(n/2^j)≤n`, so total time is linear, and the counter occupies only its bit width plus boundary cells. The attached old proof delegates to `Complexity.timeConstructible_id`; its source is not attached, so that particular witness is not certified here. |
| `computesFunInTime_polyUnary_spaceUsed` | **Supported, same witness family.** Unary `C(n+1)^e` is emitted within `c(n+1)^(e+1)` time and `c(n+1)` work space. For positive exponent, the fixed number of loop tapes each holds a side-length `n+1` bank and revisits it; output is uncharged physical output. Exponent zero uses the fixed emission chain. |
| `computesFunInTime_polyBits_spaceUsed` | **Supported with the R5 case split.** Binary polynomial value has the old time allowance and work space at most `c(C(n+1)^e+1)`. For positive coefficient and exponent, the unary intermediate, linear loop banks, and binary counter all fit that value bound. A zero coefficient requires the constant-empty family; exponent zero is another fixed-value instance. |
| `computesFunInTime_pairEncodeFixed_spaceUsed` | **Supported, same witness family.** Pairing a fixed first component with the input takes linear time and constant work space. The fixed doubled prefix plus separator is exactly a prepend instance, so zero work tapes suffice. |
| `computesFunInTime_pairFst_spaceUsed` | **Supported, same witness family.** Emit the decoded first component, or empty output on parse failure, in linear time and linear work space. The actual parser buffers at most half the original input before replay; malformed input may leave a partial buffer but never a larger visited span. |
| `computesFunInTime_pairSnd_spaceUsed` | **Supported, same witness family.** Emit the decoded second component, or empty output on parse failure, with the same bounds. The shared `pairExtractTM false true` still buffers the first component and traverses that buffer before copying the suffix; those visits remain linear in input length. |
| `computesFunInTime_pairValid_spaceUsed` | **Supported, same witness family.** Emit a singleton grammar-validity bit in linear time and constant work space. `pairValidTM` has no work tapes; alignment and the pending bit live in finite control. |
| `computesFunInTime_pairConcat_spaceUsed` | **Supported, same witness family.** On a valid pair emit the concatenated components, otherwise `[]`, with linear time and work space. `pairExtractTM true true` uses the same bounded prefix buffer, then streams the second component. |
| `computesFunInTime_pairDup_spaceUsed` | **Supported, same witness family.** Emit `pairEncode x x` in linear time with constant work space. `pairDupTM` rereads the bounded read-only input and has zero work tapes. |
| `computesFunInTime_pairLenCheck_spaceUsed` | **Supported, same witness family.** Decide the original first-component polynomial length test, rejecting malformed pairs, with time `c(n+1)^(e+1)` and space `c((n+1)^e+n+1)`. The parser/composition banks have linear spans and the captured unary output has length at most `C(n+1)^e`; the fixed coefficient `C` is absorbed in `c`. This bound deliberately keeps the linear term, including `C=0` and `e=0`. |
| `computesFunInTime_stripLast_spaceUsed` | **Supported, same witness family; R8 corrects its description.** On a valid pair, strip the second component before its last `true` and re-encode the pair; reject if no such marker exists. The guard's extraction/composition uses linear banks, `rawStripTM` buffers the original input once, and the timed conditional keeps these disjoint finite banks; their total span is linear. The quadratic time contract is retained even though the attached construction proves a stronger intermediate bound. |
| `computesFunInTime_incFixed_spaceUsed` | **Supported, same witness family.** Emit the same-width successor, or `[]` on overflow, in linear time and constant work space. This is the original zero-work-tape transducer using input scans and a finite carry flag, not the new in-place work-tape routine. |
| `computesFunInTime_pairMapSnd_spaceUsed` | **Supported as an existential target, but not by the documented old witness (R4).** It retains the original linear-plus-`Tg` time and adds `Sg(n)+c(n+1)` space, assuming monotonicity of both budgets and all-time payload space. A controller can first validate and buffer the pair, output the encoded first component, and simulate `Mg` on a buffered second component while forwarding its output. Source work-head trajectories remain unchanged, giving coefficient 1 on `Sg`, and the input buffer/administration costs only `O(n+1)`; this construction must replace the capture-all-output sketch. |
| `computesFunInTime_splitSolve_spaceUsed` | **Supported, same witness family at the requested loose bound.** The least valid split, or empty failure, keeps time degree `e+2` while using space degree `e+1`. Each actual source/body segment has time `O((n+1)^(e+1))`, hence at most that many head moves per tape from its origin; canonical round returns confine the union of reused spans to a fixed multiple of that bound. Fuel and the accepted output buffer also fit it, and the result-bearing loop reuses its banks rather than allocating a new bank per candidate. |
| `redirectTM_spaceUsedByTape` (W2) | **Supported.** For the redirected machine started from its genuine initial configuration, each tape uses exactly the source's visited count at every time. Before source halt its work actions agree; afterwards the source is halted and the redirected machine is either halted or in its stationary live loop, so the complete head trajectories still agree. |
| `computesFunInTime_cond_spaceUsed` (W3) | **Supported, same witness family.** A conditional retains the old time clause and uses at most `sD(n)+max(s₁(n),s₂(n))+c` work space. The attached timed controller keeps the decider bank, the selected branch bank, and idle branch-origin cells disjoint; only one output bit is captured from the decider. Input rewind is uncharged input-head motion, and no monotonicity is needed because both branches see the same input. |
| `exists_loopTM_spaceUsed` (L) | **Supported, same host family.** The old orbit test through indices `0,…,R(n)` retains its time clause and obtains all-time work space `c(S(n)+T(n)+1)`. Actual startup/round windows are within `T(n)`, restart body heads at the origin, and either return silently or halt with the singleton verdict; their accumulated visited sets fit fixed origin-centred intervals. The fuel word has length at most `T(n)`, and the attached host reuses its counter/capture tapes. A more explicit space derivation appears in answer 5 below. |

## Part-2 restatement-drift diffs

I extracted each original theorem signature before `:= by`, projected the new existential statement onto its time conjunct, and compared the two. Normalization removed only whitespace and the optional outer parentheses around the final time lambda. For inherited hypotheses, I removed only the new named space parameters/hypotheses listed below and compared the remainder. **No function, failure case, time exponent, quantifier order among inherited binders, or inherited hypothesis changed.**

Each row below means the original time clause is retained verbatim modulo that syntax normalization, and shows the added mathematical requirement. In the additions, `n=|x|`, `t` is universally quantified, and space is total space from `M.tm.initCfg x` unless stated otherwise.

| New row, with `computesFunInTime_…_spaceUsed` abbreviated to its suffix | Attached original | Time-clause diff | Added space / hypotheses |
|---|---|---|---|
| `id` | `Composition:137` | None: `c(n+1)` | `space ≤ c` |
| `const` | `Composition:179` | None: `c(n+1)` | `space ≤ c` |
| `prepend` | `Primitives:2122` | None: `c(n+1)` | `space ≤ c` |
| `lengthBits` | `Primitives:2137` | None: `c(n+1)` | `space ≤ c(Nat.size n+1)` |
| `polyUnary` | `Primitives:2159` | None: `c(n+1)^(e+1)` | `space ≤ c(n+1)` |
| `polyBits` | `Primitives:2183` | None: `c(n+1)^(e+1)` | `space ≤ c(C(n+1)^e+1)` |
| `pairEncodeFixed` | `Primitives:2220` | None: `c(n+1)` | `space ≤ c` |
| `pairFst` | `Primitives:2235` | None: `c(n+1)` | `space ≤ c(n+1)` |
| `pairSnd` | `Primitives:2254` | None: `c(n+1)` | `space ≤ c(n+1)` |
| `pairValid` | `Primitives:2271` | None: `c(n+1)` | `space ≤ c` |
| `pairConcat` | `Primitives:2287` | None: `c(n+1)` | `space ≤ c(n+1)` |
| `pairDup` | `Primitives:2308` | None: `c(n+1)` | `space ≤ c` |
| `pairLenCheck` | `Primitives:2783` | None: `c(n+1)^(e+1)` | `space ≤ c((n+1)^e+n+1)` |
| `stripLast` | `Primitives:2844` | None: `c(n+1)^2` | `space ≤ c(n+1)` |
| `incFixed` | `Primitives:4414` | None: `c(n+1)` | `space ≤ c` |
| `pairMapSnd` | `Primitives:2747` | None: `c(n+1+Tg n)` | Add `Sg`, `hgs`, `hSg`; `space ≤ Sg n+c(n+1)` |
| `splitSolve` | `Primitives:4393` | None: `c(n+1)^(e+2)` | `space ≤ c(n+1)^(e+1)` |
| `cond` | `Wrappers:711` | None: `c(T₀ n+max(T₁ n)(T₂ n)+1)` | Add `sD,s₁,s₂,hsD,hs₁,hs₂`; `space ≤ sD n+max(s₁ n)(s₂ n)+c` |
| `exists_loopTM_spaceUsed` | `Loop:2519` | None: `c(T n+1)(R n+2)` | Add `S,hFspace,hstartSpace,hroundSpace`; `space ≤ c(S n+T n+1)` |

The two nonexistential Part-2 rows intentionally have different shapes:

```diff
 capture_run parameters:
   tm, host, emb, ret, hagree, pre, out₀, c₀, t, hlive
-  conclusion: one endpoint configuration equality
+  capture_visitedByTapeHead: selected visited-set/cardinality equalities
+                            and capture growth bound
```

The source-agreement equation and strict-before-`t` liveness hypothesis are unchanged; the endpoint equality is available from the original theorem and need not be repeated.

```diff
 redirectTM_computes / redirectTM_live:
   verdict-dependent computation/nonhalting contracts
+  redirectTM_spaceUsedByTape:
+    every M, haltOn, x, t, source tape i;
+    redirected per-tape space = source per-tape space
```

W2 is a new unconditional property of the same named transformer, not a textual restatement of those verdict-dependent contracts. That is consistent with the pack's declared W1/W2 per-tape exception. In particular, it does not silently require either an eventual halt or a matching last output bit.

## Adversarial instantiations

These tests are separate from the general proofs. “Pass” means the tested boundary supports the stated theorem; “gap” concerns the claimed interface coverage.

| # | Instantiation | Result |
|---|---|---|
| A1 | `transferTM`, distinct indices, both source and destination empty, another tape nonempty | Pass: exact trajectory `0,-1,0`, first exit 2, both touched tapes use 2 cells, frame word unchanged. The witness cannot be `T=0`. |
| A2 | `compareTM`, `[true]` versus `[true,false]`, and the reverse orientation | Pass: verdict false, first exit 4, trajectory `0,1,0,-1,0`, 3 visited cells. The shorter first tape does not terminate rewind early. |
| A3 | `compareTM`, `[false]` versus `[true]` | Pass: immediate mismatch gives first exit 2 and visited set `{-1,0}`; no right overshoot occurs. |
| A4 | `compareTM`, `fst=snd`, word `[true,false]` | Pass: true verdict in 6 steps, visited set `{-1,0,1,2}`. The Boolean disjunction selects one action, so there is no double move. |
| A5 | `incrementTM` on `[]`, `[false]`, and `[true,true]` | Pass: respectively overflow in 2 steps, success in 2 steps producing `[true]`, and overflow in 6 steps producing `[false,false]`. All heads return to zero. |
| A6 | `copyTM`/`transferTM`, `src=dst` | Their run/space hypotheses correctly reject the instantiation via `hne`. No theorem quietly asserts destructive self-transfer preserves a nonempty source. |
| A7 | `k=0` | Tape-indexed Part-1 contracts have no possible `Fin 0` argument. Forwarding embedding at `m=k=0` and seam composition at `k=0` remain meaningful, with total work space 0. Silent embedding into a zero-tape host has no capture index. |
| A8 | Surjective `ι` | Forwarding frame statements become vacuous only for off-bank tapes, as intended. Silent `hcap` is impossible; selected-tape lockstep itself is still nondegenerate. |
| A9 | Silent embedding, long `pre`, nonempty initial source output, one final halting emission | Pass: capture starts at the old total length and visits exactly two cells in that one-step window; all old recorded bits remain. Gap R1: the final source halt is still an actual host halt, not a continuation state. |
| A10 | Seam `T₁=T₂=0` | Pass: the hypotheses identify the corresponding entry/exit seam fields; the composite executes exactly one silent dispatch. Per-tape visited sets stay `{0}`. |
| A11 | Seam `entry=q₂`, `T₂>0`, with phase two stationary | `_run` and the space clauses pass. `_firstReturn` cannot apply: its second cut already fails at zero; actual first arrival is at dispatch. |
| A12 | Phase two halts at some time strictly before `T₂` | Impossible under `h₂`: halt absorption makes the state at `T₂` `none`, contradicting its specified live `q₂`. This is not a counterexample to composition. |
| A13 | Positive source return to its own entry, changing a tape | Gap R3: two steps can write `[true]` and return from anchor to itself with no positive intermediate anchor visit; `seamCompTM` dispatches immediately instead. |
| A14 | Off-bank frame head `7`, or forwarded accumulated output `[true]` | R1 equations pass. Gap R2: no `Cfg.ofWords` can describe the required seam, so the supplied composition theorem cannot be instantiated. |
| A15 | `pairMapSnd`, unary-square payload with linear work space, input `pairEncode [] b` | Gap R4: the existing capture tape visits quadratically many cells; the claimed linear administrative bound cannot describe it. The alternative streaming existential remains feasible. |
| A16 | `polyBits C e` with `C=0,e=1` | Gap in the sketch, not the theorem: the old generator retains a linear bank while the new bound is constant. A constant-empty witness satisfies the statement. |
| A17 | Loop `R=0` | Pass: the conclusion tests `s0 x` once, and zero fuel is a width-zero word. Borrow overflow and its boundary steps are absorbed by the `+1` and fixed constants. |
| A18 | Loop `T=0` at an input | Hypotheses are inconsistent: `hInv0` makes an admissible round available, while `hround` requires `0<t≤0`. There is no zero-budget trivialization of an arbitrary predicate. |
| A19 | Loop rounds alternate leftward and rightward excursions from origin | Pass with a constant-factor union bound, not a bare per-round maximum. Individual origin-containing intervals of at most `S` cells can have union of `2S-1` cells; the stated unspecified constant permits this. |
| A20 | W1 initially halted source with `t=0`; W2 source never emits | W1's guard is empty and both compared visited counts are one per tape. W2 goes to the stationary live loop if the empty register never matches, preserving the source's post-halt work positions exactly. |

For the two important interface failures, the traces are formal and do not rely on finite testing:

* **Halting emission.** Take source state type `Unit`, no source work tapes, and the action `(input move 0, no work action, output some true, state none)` at its sole state `q`. Embed silently into one host capture tape with empty prefixes. Then
  \[
  c_0.state=\mathrm{some}\ q,\quad
  c_1.state=\mathrm{none},\quad
  c_1.workTapes(0)(0)=\mathrm{some}\ true,\quad
  c_1.workTapePos(0)=1.
  \]
  For every later time the closed host stays at `c₁`. The only possible seam exit label is `q`, but selecting it replaces the first source action by dispatch and leaves the capture tape empty. Thus neither choice executes that source action and then continues through the current closed-embedding/seam interface.

* **Positive self-return.** Take one tape and two source states `q,r`, with `q` writing `true` at its current cell, staying at that cell and entering `r`, and `r` staying and returning to `q`. From the empty canonical word,
  \[
  M.runFrom(\operatorname{ofWords}q\,[])\,2
   =\operatorname{ofWords}q\,[true],
  \]
  and the only strictly positive interior state is `r`. With seam exit `q`, however, the composite's first transition performs no write and enters the next phase. The weaker positive-interior cut cannot justify the unmodified composite.

## Answers to the six numbered questions

### 1. Is the closed R1 shape sufficient for the three consumer families?

**Not for the full advertised scope.** It is sufficient for exact relocation of a closed computation onto a fixed subset of physical tapes. It combines directly with the current R2 theorems when both phases have canonical, silent, live endpoints and the required cuts include time zero.

| Family | Supported directly | Remaining gap |
|---|---|---|
| Chapter-1/2 retrofit | Distinct-entry/exit silent canonical routines on fixed physical banks, including the new transfer/copy/clear routines. | `emitterP2_call_segment` handles positive return even if entry equals exit; `emitterP2_relocate_run` supports arbitrary frames/configurations; returning wrappers retain halting emissions and source residue. R1–R3 identify why these are not obtained from the new exports. |
| Hennie–Stearns zones | Embedding a one- or two-tape primitive into an actually distinct physical bank; framing additional physical tapes. | Selecting whole tapes does not relocate a zone within a tape, multiplex logical tapes, or shift coordinates. The consumer table needs a concrete map through the representation layer; R1 itself cannot turn three physical source tapes into two. |
| Two-work-tape universal machine | Routines already expressed on a fixed physical tape subset, using the same physical input and a compatible seam. | Virtual-input interpretation, encoded-zone access, returning control, and noncanonical local frames need additional interfaces or consumer-specific constructions. The packet does not contain that consumer's implementation, so full adequacy is not established. |

The halting-emission example is a concrete subroutine step that the claimed `embed`-then-`seam` combination cannot express while preserving the source action and continuing. The attached public `exists_installCallTM` is not a substitute for its exact configuration-preserving contract: it computes from a word argument, cleans scratch, changes the witness/tape layout, and has a different cost guarantee. Its own exported positive-return shape also needs the R3 repair before generic R2 chaining can consume it without an extra premise.

### 2. Is `T₁+1+T₂` exact, including the requested edge cases, and does first return support chaining?

**The run equation and space clauses are correct; unrestricted consumer chaining is not delivered.** There are `T₁` source transitions, one silent dispatch, and `T₂` second-phase transitions. `T₁=0` is valid: the starting configuration is already the left exit seam, and dispatch is still one real step.

When `entry=q₂` and `T₂>0`, `_run` only asserts equality at the indicated later time; it does not assert that this is the first visit to the right anchor. The additional cut required by `_firstReturn` fails at zero. A strict interior halt is ruled out by absorption and the live endpoint in `h₂`.

For phases satisfying the stated cuts, induction does permit three or more phases: use `_run` for the composite endpoint and `_firstReturn` for its cut, then compose again. This requires the usual decidable equality on whichever state sum becomes the next left operand; finite machine states supply it. The same procedure cannot consume the more general positive-return promises in the existing clean-call exports without a fresh-entry adapter. Thus the theorem is sound, but the unqualified “so composites chain” description needs its hypothesis qualification and R3's missing interface.

The sharp max corollary also has the correct condition. “Idle” here means **no head movement**, not no writing: a phase may change the cell under a stationary head while still visiting only `{0}`. Neither the proof nor its intended space conclusion requires a no-write ownership condition.

### 3. Do all Part-1 constants and space intervals hold?

**Yes, for the theorem statements.** The independent table and invariants establish every turn, rewind, entry, and boundary contribution. Transfer/copy finish at `2L+2`; their `3L+3` bounds are deliberate slack, so they should not be described as exact elapsed costs. Clear and overflow increment attain `2L+2`; successful increment takes `2p+2`; compare takes `2d+2`.

Equal-prefix unequal-length comparison reaches the shorter word's blank at position `min`, moves left immediately, and returns in `2min+2`. It does not inspect position `min+1`, even when the first word is longer. Equal words likewise turn at their first double blank at position `min`. The space theorem is therefore correct in every mismatch position, but the sketch's `[-1,min+1]` interval does not establish it; use `[-1,min]`, or the exact `[-1,d]`.

All Part-1 contracts explicitly preserve the complete seam configuration, not merely the output word or control. Input stays at 1, physical output stays empty, all active heads return to 0, and unselected words stay unchanged. All-time space follows from the stationary exits, as derived above.

### 4. What drift and witness-honesty problems occur in Part 2?

**No mathematical drift in the 19 time clauses or inherited hypotheses.** The complete comparison is above; W1 and W2 retain their intentionally different nonexistential forms. Every existential row correctly puts time and all-time space on one witness, with one coefficient that can be enlarged to cover both bounds.

The serious witness issue is `pairMapSnd`, not `stripLast`. To make the obstruction explicit, let the payload be the attached unary generator with coefficient 1 and exponent 2, and write `N=|b|`. It has a fixed finite number of unary banks and a valid bound `Sg(N)≤a(N+1)` for a machine constant `a`; its output has length `(N+1)^2`. On the valid input `pairEncode [] b`, whose length is `N+2`, the old outer capture tape alone gives

\[
\begin{aligned}
\text{old host space}&\ge (N+1)^2+1,\\
\text{claimed bound}&\le a(N+3)+c(N+3)=(a+c)(N+3).
\end{aligned}
\]

For any proposed fixed `c`, set `N=4(a+c+1)`. Then

\[
N+1\ge N,\qquad N+3\le 2N,\qquad N>2(a+c),
\]
so
\[
(N+1)^2+1>N^2>2(a+c)N\ge(a+c)(N+3).
\]

Thus that witness family cannot satisfy the advertised linear administration bound. This refutes the sketch's witness claim, **not** the existential statement: validating and emitting the retained prefix before forwarding the payload avoids the capture bank.

`polyBits` is honest in the positive coefficient/exponent regime; the stored unary intermediate is exactly why its space is linear in the polynomial **value**, not logarithmic in input length. At `C=0`, its old unary-loop witness still moves through `n+1` cells on each loop tape, so a constant witness branch must be recorded. `stripLast` retains a linear-size raw buffer and linear-size guard banks and meets the new bound with its existing family. The sharp original `lengthBits` witness remains an explicit evidence limit because its supplying module is absent.

### 5. Does the loop space row follow from the budget-limited round hypotheses, and should fuel use `Nat.bits (R n)`?

**The stated row is sound. The fuel's actual width is `|(Nat.bits (R n))|`; `T n` is a valid upper bound, not its definition.** Fix an input of length `n` and put
\[
\ell=|(Nat.bits(R n))|.
\]

1. `hstart` and `hround` give the actual startup/return/halt times at most `T n`. Every prefix used by the host lies inside one of those windows, so `hstartSpace` and `hroundSpace` apply. Bounds on longer, uninterrupted body executions are unnecessary; the source can have different behavior after the intercepted return without affecting this argument.
2. Each body phase starts with all work heads at 0. A unit-step integer walk that visits at most `S n` cells stays within `[-S n,S n]`; therefore the union over **arbitrarily many rounds** on each fixed body tape is still contained in that interval. Summing over the fixed `body.k` tapes gives at most `body.k·(2S n+1)`, with no factor `R n`.
3. `hFspace` bounds the fuel machine's own bank by `S n` throughout its execution. Those tapes are retained but not reused afterwards in the attached host, so their contribution does not increase.
4. `hF` starts from empty output and permits at most one emitted bit per step. Hence
   \[
   \ell\le T n.
   \]
   The fuel capture tape and copied countdown tape each need only the interval from the left overshoot to position `ell`, plus fixed controller allowances. Debit changes bits inside the same fixed width, including the final overflow; it never appends a new width.
5. Startup and rejecting body rounds end with empty output, so append-only output forces them to emit nothing throughout. An accepting round ends with exactly `[true]`, so its capture grows by at most one bit. The capture tape was already rewound/cleared after fuel installation; no per-round output log accumulates.
6. The stationary one-cell flag and finitely many boundary allowances add a machine constant. Thus one can choose a constant `c`, independent of `x`, `t`, and the number of rounds, with
   \[
   \text{host space}\le c(S n+\ell+1)\le c(S n+T n+1).
   \]
   The known time contract ensures eventual halt; after halt the visited set is constant, so the bound extends to all `t`.

The existing statement is therefore a valid, looser fuel bound. A sharper `S n+|(Nat.bits(R n))|+1` conclusion is a useful additive theorem, not a required correctness repair. Replacing it by a per-round maximum with coefficient 1 would need stronger fixed per-tape interval hypotheses: repeated origin-based walks can explore opposite sides of the origin.

The stated space hypotheses are somewhat stronger than necessary because they bound all source times up to the full round budget, even beyond an earlier return. This causes no soundness problem. If it obstructs a concrete consumer, a future refinement may attach the space bound to every prefix of the particular witnessed first-return interval, rather than silently changing the current contract.

### 6. Which boundary sanity statements are missing?

The following small public or audit-only statements would pin down the risky cases. They need not replace the general contracts.

| Proposed check | Required result |
|---|---|
| S1: empty transfer/copy | With distinct indices and both words empty, first exit is exactly 2; active visited sets are `{-1,0}`; every other word is preserved. |
| S2: self-comparison | For `fst=snd`, first exit is exactly `2\|w fst\|+2` with `done true`, original words, and one physical head move per step. |
| S3: proper-prefix comparison | For `u` versus `u ++ b :: v`, in both orientations, first exit is exactly `2\|u\|+2`, verdict false, visited interval `[-1,\|u\|]`. |
| S4: immediate successful carry | On `false :: rest`, first exit is 2, verdict true, resulting word `true :: rest`, and visited set `{-1,0}`. |
| S5: width-zero overflow | On `[]`, first exit is 2, verdict false, empty word retained, visited set `{-1,0}`. |
| S6: zero-duration seam phases | If `T₁=T₂=0`, composite endpoint occurs after the single dispatch; visited sets equal the original origin singletons, including total space zero for `k=0`. |
| S7: positive self-return adapter | Under the repaired interface, a two-step call that starts/ends at the same anchor actually performs both source actions before dispatch, preserving the changed word. This must fail as an instantiation of the unrepaired strict-zero-cut interface. |
| S8: final halting emission into a return state | Under the repaired returning embedding, a one-step source halt captures/forwards that step's bit and lands in a live return with source tapes/heads preserved. Include nonempty capture and physical-output prefixes. |
| S9: arbitrary-frame composition | Under the generalized seam theorem, an unowned head at 7 and a pre-existing output prefix are preserved; dispatch is still one step and adds no visited cell. |
| S10: zero polynomial coefficient | Explicitly exhibit the constant witness for `polyBits 0 e` with constant space for every `e`; do not instantiate the unary-bank family. |
| S11: long payload with small work space | Instantiate the chosen `pairMapSnd` controller with the unary-square payload, proving the stated space bound for that actual controller. This rules out accidentally retaining the old output-capture implementation. |
| S12: loop exhaustion and accumulated span | At `R=0` test the initial orbit point once; for alternating left/right excursions prove the union interval bound and show that the counter width never grows during debit. |

## Frozen decisions and recommended repair boundary

* **12.1:** Honored mathematically. The visited-set headline is sharper than a scalar sum; the singleton-idle hypothesis correctly yields the per-tape maximum. Equality of the union is available, but containment already gives the requested bounds.
* **12.2:** The new catalog is in a separate file and the attached old files contain no new admissions. Historical byte identity still requires comparison to the prior pinned baseline; it cannot be certified from this packet alone.
* **12.3:** I accept the explicit 2026-10-08 clarification placing P16–P18 with the lazy emitter scope. P7 is covered by the unary polynomial family, P8 by the threaded length check, the realized bounded split search is covered, and P12 now has the named clear routine. R10 records the precise limitation of annotating only the decision-loop export; no undeclared theorem for the other loop shapes should be assumed.
* **12.4:** Honored: two named closed emission-policy transformers share one private action core. They are valid primitives; R1 asks for the additional returning interface their advertised consumers need.

To close this gate, resolve R1–R3 with concrete exported contracts and consumer instantiations, and resolve R4 by choosing either the stronger-space captured witness or the new forwarding controller. The three minor repairs should be included in the same statement revision. Preserve the existing correct bounds and the zero-drift time contracts; the findings do not justify weakening them indiscriminately.

The suggested repairs are interface/construction proposals, not completed Lean implementations. In particular, no formal proof of a repaired returning adapter or streaming threaded-map machine is claimed in this report.

## Notation glossary

Existing Lean identifiers and their bound variables retain the meanings in the attached sources. Local explanatory notation used here:

- `L`: length of the word touched by a single-tape sweep or carry routine.
- `d`: compare's first differing or terminating-blank position, bounded by the shorter length.
- `p`: position of the first `false` in a successful fixed-width increment.
- `n`: physical input length `|x|` in the space/diff discussion.
- `N`: payload length `|b|` in the threaded-map witness counterexample.
- `a`: fixed linear-space coefficient for that unary-square payload machine.
- `ell` / `ℓ`: actual binary fuel-word length `|(Nat.bits(R n))|`.
- `q,r`: source control states used only in the two explicit counterexamples.
- `c₀,c₁`: initial and one-step configurations in the halting-emission counterexample.
- `ofWords q []` and `ofWords q [true]` in the single-tape counterexample abbreviate the corresponding constant `Fin 1 → List Bool` word assignments.
- `[-1,L]`, `[-1,d]`, and similar intervals in visited-set claims mean the integer points of those intervals.
