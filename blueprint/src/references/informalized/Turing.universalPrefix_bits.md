<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalPrefix_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Parser on Paired Bits

**Claim.** After $2j$ steps on the encoded input, for $j\le |\alpha|$, the prefix parser is ready to read the first half of the next pair, its input head is at position $2j+1$, and its output is the first $j$ bits of $\alpha$.

**Proof.** Induct on $j$. At $j=0$, the initial configuration already has the parser in the state expecting a bit pair, the head at position $1$, and empty output; equality of these configurations follows from extensionality for configurations with no work tapes (`Cfg.ext_zero_tapes`). For the successor step, assume the description after $2j$ steps and use $j<|\alpha|$ to identify both positions $2j$ and $2j+1$ of the encoded input as copies of $\alpha_j$ (`universal_pair_get`). The first parser step reads the first copy and moves right; the second reads the matching copy, emits $\alpha_j$, and moves right again. These transitions are instances of the one-step description (`universalPrefix_step`), and the input-symbol lemma identifies the scanned symbols at the two head positions (`inputSymbol_at`). The head therefore advances from $2j+1$ to $2(j+1)+1$, while appending $\alpha_j$ to the previous output. The list identity for taking a successor prefix, together with the induction hypothesis, gives output $\alpha.take (j+1)$. The resulting state, head position, and output are the required ones.

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.universal_pair_length`, `Turing.universal_pair_get`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.universalPrefix_step`, `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`.
