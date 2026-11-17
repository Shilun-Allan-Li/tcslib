<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of a simulated step

**Claim.** Under the stated head-position and blank-cell hypotheses, the simulator’s right-extension phase, after the specified number of steps, reaches the canonical starting configuration encoding the source machine’s next configuration over the enlarged zone.

**Proof.** 1. Let $s$ be the stored read information at coordinate $a+n$, let $R$ be the encoded zone through coordinate $a+n-1$, and let $W$ extend that zone by the row at $a+n$. The head bound ensures that the stored symbols in $s$ are exactly the work-tape symbols under the source machine’s heads. The blank-cell hypothesis and the same head bound show that the new row is exactly the row formed from $s$ with the required head markers. Consequently $W=R$ followed by that row. Reversing the encoded lists therefore identifies the simulator’s current buffer with the reversed encoding of $W$ followed by the boundary marker.

2. The simulator first finishes its right-extension pass. The guard row is the row determined by $s$, so the completed buffer has the form just identified. The transition then reads the source input symbol and the stored work symbols, applies the source machine’s prescribed action, moves the input head in the corresponding way, and emits exactly the output appended by that action. Here the simulation’s input-reading property is supplied by `sweepInput_read`, the input-position compatibility by `sweepPos_move`, and the reversal with its buffer update by `sweep_turn_left`. The result is the backward-facing write phase, with the frontier shifted left by one and the boundary marker at the head of the right stack.

3. During the write pass, the visited cells are exactly the cells of $W$ in reverse order. Since all source heads lie strictly before the right endpoint, the initial right-marker state at that endpoint is false. The write-fold identity (`write_zone`) then says that processing these cells produces exactly the zone rows of the updated source configuration, with the appropriate head positions. The zone has $(n+2)k$ cells (`tapeZone_length`), so the reverse sweep lemma (`sweep_run_reverse`) applies for precisely that many steps and yields the updated encoded zone, in its required order.

4. At the end, the simulator takes one transition from the write phase into the left-extension phase. The tape reads the boundary marker there by `sweepTape_read`, and a zero-motion transition leaves the reversed encoding in place by `sweepRevCfg_stay`. Decomposing the total run into its final single steps and the intervening block runs (`runFrom_succ_eq_step'`, `runFrom_add`), the right-extension block lemma (`sweep_grow_right_block`) and the reverse-sweep calculation above assemble these phases into exactly `sweepStart` for the updated source configuration, with the stated enlarged zone and frontier.

**Key facts.** `Turing.FinTM.sweepInput_read`, `Turing.FinTM.sweepPos_move`, `Turing.FinTM.sweep_turn_left`, `Turing.FinTM.write_zone`, `Turing.FinTM.tapeZone_length`, `Turing.FinTM.sweep_run_reverse`, `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepRevCfg_stay`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.sweep_grow_right_block`.
