<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satScan_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Scanner Step

**Claim.** For a Boolean word $x$, state $q$, and position $i<|x|$, one scanner step from the configuration at position $i$ with empty output reaches the configuration at position $i+1$ in state $\delta(q,x_i)$, still with empty output.

**Proof.** The configuration’s shifted head coordinate is $i+1$, and the strict bound $i<|x|$ places it on an input symbol. The input-symbol identification lemma (`inputSymbolInner`) therefore says the scanner reads $x_i$. By the scanner’s transition definition, reading a bit moves the head right, changes the state to $\delta(q,x_i)$, and emits nothing. The right-move lemma (`moveInputPos_pos_of_ne_right`) identifies the resulting shifted position as $i+2$, corresponding to unshifted position $i+1$. Finally, since there are no work tapes, equality of state, input position, and output suffices for equality of configurations (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
