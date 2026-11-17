<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSource_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Unary Output

**Claim.** The machine that emits a fixed prefix of $C$ ones halts after $C+1$ steps on the prescribed empty-input bank configuration, with output the word of $C$ ones and unchanged work-tape contents and head positions.

**Proof.** With zero work tapes, the prescribed bank configuration is exactly the machine's initial configuration: their states, input-head positions, and outputs agree, and `Cfg.ext_zero_tapes` gives equality of configurations from those components. After $C$ emission steps, the prefix-emission result (`catalogPrefixTM_emit`) identifies the configuration as the prefix machine's state after emitting the first $C$ symbols of the word of $C$ ones. Since the word has length $C$, these are all its symbols. One further transition sees the end of the empty input and halts. Unfolding this transition shows that the output remains the word of $C$ ones and that the input position is unchanged; with zero work tapes, there are no tape contents or head positions to change.

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.catalogPrefixTM_emit`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
