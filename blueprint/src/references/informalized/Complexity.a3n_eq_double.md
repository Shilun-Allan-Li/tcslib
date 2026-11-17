<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a Doubled Bit

**Claim.** When $y=pre\,b\,b\,rest$, the comparator in parser state at position $|pre|+1$, with work word $u$ and its head at $|u|$, advances two steps to parser state at position $|pre|+3$, with work word $ub$ and its head at $|ub|$.

**Proof.** At the first input position, the input-symbol lemma identifies the scanned bit as $b$ (`inputSymbolInner`). In parser state, the comparator moves right and branches according to that bit, leaving the work tape unchanged. At the next position the scanned symbol is again $b$. The selected branch writes that bit at the current work-head cell, advances both heads, and returns to parser state. The work tape therefore represents $u$ followed by $b$, and its head is at the new end position; the input head has advanced twice. The buffer-extension identity verifies the updated tape contents (`bufferTape_append`), and the two single-step transitions combine into the two-step run using the successor and zero-time run identities (`runFrom_succ_eq_step`, `runFrom_zero`).

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
