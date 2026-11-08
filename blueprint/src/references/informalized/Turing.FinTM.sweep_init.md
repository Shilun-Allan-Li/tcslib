<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization reaches the canonical start

**Claim.** After exactly $2k+2$ steps, the single-tape simulator started on the encoded input reaches the canonical configuration for the source machine’s initial configuration, with a one-block zone starting at coordinate zero and its work head at coordinate $-1$.

**Proof.** First identify the encoded input-head position as $1$, and observe that the simulator’s initial work tape is blank everywhere; thus its initial configuration has the stated simple forward-facing form. The simulator’s initialization block writes the marked blank row in $k$ steps, by `sweep_init_block`. It then takes the transition that turns back across the block. The reversal lemma `sweep_run_reverse`, with the identity visit operation, carries the marked row back across the tape; the fold is unchanged by `sweepFold_id`. This places the boundary marker at the frontier. The next transition writes the boundary marker onto the right stack and enters the source machine’s initial state, by `sweepRevCfg_write`. The resulting work tape is blank at the relevant head position, so this transition has the required form. The decomposition of the run into these blocks and final steps follows from `runFrom_succ_eq_step'` and `runFrom_add`; the zero input-head motion is justified by `moveInputPos_zero`. Combining the phases gives frontier $-1$ and the canonical encoding of the source initial configuration over one block at coordinate zero.

**Key facts.** `Turing.FinTM.sweepFold_id`, `Turing.FinTM.sweep_init_block`, `Turing.FinTM.sweep_turn_left`, `Turing.FinTM.sweep_run_reverse`, `Turing.FinTM.sweepRevCfg_write`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.moveInputPos_zero`.
