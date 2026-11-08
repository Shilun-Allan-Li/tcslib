<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.prefixTM_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-copying phase

**Claim.** For binary strings $w,x$ and each $i\le |x|$, after $i$ steps from the configuration in the final prefixing state, with input head at position $1$ and output $w$, the machine remains in that state, its input head is at position $i+1$, and its output is $w$ followed by the first $i$ bits of $x$.

**Proof.** Proceed by induction on $i$. At $i=0$, the given configuration already has the final prefixing state, head position $1$, and output $w$; these are exactly the claimed values because the length-zero prefix of $x$ is empty. For the successor step, assume the claim at $i$ and use the one-step recurrence for runs (`runFrom_succ_eq_step'`). Since $i<|x|$, the input symbol at head position $i+1$ is the bit $x_i$ (`inputSymbolInner`). In the final prefixing state, the transition outputs that bit, stays in the same state, and advances the input head by one. The head movement gives position $i+2$ (`moveInputPos_pos_of_ne_right`), and appending the emitted bit to the prior output gives $w$ followed by the first $i+1$ bits. Equality of configurations follows by checking state, head position, and output; with zero work tapes these determine the configuration (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
