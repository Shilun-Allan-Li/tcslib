<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.decrementTM_run_underflow_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement underflow

**Claim.** Under the stated hypotheses, if decrementing $w$ underflows, then after $2|w|+2$ steps the decrement machine reaches the done phase with false flag and writes a word of $|w|$ true bits in the indicated cells; it does not reach a done phase earlier, and the stated head-position bounds hold.

**Proof.** Complement $w$ bitwise. The complement identity for fixed-width counters converts the assumed decrement underflow into overflow for increment on the complemented word (`counter_dec_complement`). The buffer identity shows that the complemented initial tape agrees with the buffer for that word (`counter_buffer_complement`). Apply the increment overflow theorem to this complemented configuration. It gives the done phase with false flag after $2|w|+2$ steps, writes $|w|$ false bits, has no earlier done state, and satisfies the head bounds. The run correspondence between decrement and complemented increment (`counter_decrement_run`) transfers the run, early-state exclusion, and head bounds back to the original machine. Complementing the written false bits gives $|w|$ true bits, as required.

**Key facts.** `Turing.counter_dec_complement`, `Turing.counter_buffer_complement`, `Turing.incrementTM_run_overflow_ofCfg`, `Turing.counter_decrement_run`.
