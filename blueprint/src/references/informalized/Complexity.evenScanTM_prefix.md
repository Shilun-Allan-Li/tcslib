<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Examples.lean :: Complexity.evenScanTM_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity scan prefix invariant

**Claim.** After $j\le |x|$ steps, the even-parity scan machine's state records whether the prefix of length $j$ has even parity, its input-head position is $j+1$, and its output is empty.

**Proof.** Proceed by induction on $j$. At $j=0$, the machine is in its initial state, the empty prefix has even parity, the head position is $1$, and no output has been written. For the successor step, assume the three assertions at $j$ and use $j<|x|$. The input-symbol lemma identifies the symbol under the head as $x_j$ (`Turing.FinTM.inputSymbol_at`). The run successor identity reduces the next configuration to one machine transition (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). The transition toggles the parity state exactly when $x_j$ is true; since the prefix of length $j+1$ is the old prefix followed by $x_j$, this state records whether its number of true bits is even. The transition moves the head one position to the right; the right-move identity gives position $j+2$ (`Turing.moveInputPos_pos_of_ne_right`). It writes no output, so the output remains empty. These are the three assertions for $j+1$.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_pos_of_ne_right`.
