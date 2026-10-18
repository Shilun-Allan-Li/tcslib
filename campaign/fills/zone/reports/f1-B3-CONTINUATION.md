# ZF-B3 continuation: concrete uniform simulator

The frozen target is still admitted. No theorem claiming a physical universal simulator has been completed. The 16 new private declarations in `Codes2Tape.lean` isolate proved semantic obligations and a finite-machine deadline test; the existing effective scheme and all 24 received privates remain byte-identical.

## Use the completed pieces

- `zfB3_decode_length`: decoded serialization has length at most `max α.length 354`, including malformed codes. This is a data-size bound, not a polynomial-time canonizer theorem.
- `zfB3_decode_states`: `351 * ((zfBDecode α).numStates + 1)` has the same bound.
- `zfB3_guard_failure`: a failed length guard selects the fallback before any invocation of the state/table readers in the pure parser. No binary arithmetic machine cost is asserted.
- `zfB3Output`, `zfB3Emit`, and their three laws: the three finite output classes and the exact append update, including a final halting emission.
- `zfB3Clock_correct`: induction identifies the semantic countdown result with the state and output summary after exactly the permitted number of transitions. This is not the physical countdown implementation.
- `zfB3Answer_correct`, `_zero`, and `_malformed`: exact bounded acceptance, the zero-deadline rejection, and rejection at every deadline for a malformed code.
- `zfB3_deadline_test`: a real finite machine, assembled only by public pairing extraction, comparison, and pointwise composition. It outputs `[false]` on zero and `[true]` as a continuation flag on a positive deadline. It is not an acceptance decider on positive deadlines. The coefficient is explicit and uniform.
- `zfB3_uniform_of_simulator`: supply a single finite machine computing `[zfB3Answer α x t]` in `C * (α.length + x.length + t + 1)^e`. The lemma constructs the concrete effective scheme through `codePrim_machine zfBCanonical zfBPrimCanonical` and proves both frozen uniform fields at degree/coefficient `C + e + 1`. It does not assume or infer a polynomial bound on the arbitrary-time canonizer.

## Requested shared lemmas

Request a public fixed-width decrement routine and its arbitrary-configuration run contract in `Build/Catalog.lean`, by promotion/generalization of the existing machinery: the pure `loopDebit` / `loopValue` laws and `loopHost_borrow*` proofs in `Build/Loop.lean`, and the standalone `f2_loopDebitTM` / `f2_loopBorrow_correct` implementation in `Build/Catalog.lean`. Do not create another implementation in Codes2Tape.

Required shared contract, stated without committing to new public names:

1. One designated counter tape carries a little-endian Boolean word at its current head. It agrees with `FinTM.bufferTape word` at relative positions `-1` through `word.length`, inclusive. Other cells and tapes, other head positions, native input position, and output prefix are arbitrary.
2. From the borrow-entry control, decrement the word in place without changing its width. A nonzero value becomes one less and returns success. A zero word wraps to all true and returns underflow. Width zero returns underflow in two steps. The existing pure debit function supplies these semantics; expose its value and width laws rather than reproducing them.
3. Return to the initial counter head, preserve every other head, native input position, output, and cells outside the counter interval. A bound `2 * word.length + 2` suffices here; the existing sharper `2 * leadingZeroCount + 2` may be retained.
4. Include positive duration, no earlier return to either exit anchor, and the translated through-run head bound. These are the seam hypotheses needed when the two simulated work heads remain displaced.

The currently added `transferTM_run_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, and both increment framed rows are themselves admitted at this base. Their proofs must land before they are cited. This delivery neither uses them as axioms nor privately reconstructs them. The decrement request is additional to that five-row batch; increment is not decrement.

This is a request for shared implementation under the no-copy rule, not a counterexample to the target, not a claim that no alternative algorithm exists, and not a claim that one shared theorem alone completes the simulator.

## Remaining construction, in order

1. Implement the nested-input setup with the deadline and claimed state count stored in binary. The actual binary comparison of `351 * (n + 1)` with the remaining code length must precede state-indexed work. The new size/guard lemmas prove the semantic facts but do not implement this comparison.
2. Validate initial and successor ranges, the 27 seven-field records per state, canonical count bits, and the all-true suffix, agreeing exactly with `zfBDecode`. On failure choose the fixed silent fallback. The existing primitive-recursive compiler cannot discharge this time bound.
3. Implement table lookup and application, keeping the two source work tapes on two physical tapes. Keep administration and buffered virtual input separate; cite `Turing.vhostEmitTM` / `vhostSilentTM` and the embedding/seam layers. A family of hosts parameterized by the decoded machine is not one uniform finite interpreter.
4. Assemble the content-dependent binary countdown through the requested shared routine. At zero reject. At positive deadlines apply the permitted source transitions and inspect the successor of the final one before timeout. Use the proved three-state output semantics.
5. Maintain a per-input cost ledger and prove one `C,e` bound for both results. `exists_loopTM` and `exists_loopCfgTM` currently take `R : ℕ → ℕ`, fuel `Nat.bits (R input.length)`, and canonical `stateWord` seams. Neither their length-only horizon nor a length-only exponential envelope proves the required budget for the particular numeric deadline. Do not reset or serialize the two source tapes to force this interface.
6. Apply `zfB3_uniform_of_simulator`, replace the sole remaining original admission, run the exact checker directly on Codes2Tape and the facade, print both headline axioms, and lint.

## Freeze and scope

Only Codes2Tape is owned. The two imports `Build.VirtualInput` and `Build.Catalog` were added under B3 permission. Removing those two lines and the single new preparation section reproduces the complete received file byte-for-byte. No source statement was weakened, no old helper or proof was edited, and no ND existence theorem is used.

Notation: `α` is the code word, `x` the payload, `t` the numeric deadline, `C` a uniform time coefficient, and `e` a uniform time exponent.
