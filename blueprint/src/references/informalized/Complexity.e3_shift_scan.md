<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_shift_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan Invariant of the Zero-Prefixing Machine

**Claim.** For every pair of binary words $w,x$ and every $t\le |x|$, after $t$ steps from its initial configuration the machine defined from $w$ is in its scanning state, its input head is at position $t+1$, and its output consists of exactly $t$ zero bits.

**Proof.** Proceed by induction on $t$. At time zero, the initial configuration is in the scanning state, its head is at position $1$, and its output is empty, which is the list of zero bits of length zero. For the successor step, the induction hypothesis and $t+1\le |x|$ ensure that the head is on input bit $x[t]$. The input-symbol rule identifies the symbol there (`Turing.inputSymbolInner`). The run-step equation expresses the next configuration as one transition (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). In the scanning state, the transition preserves that state, moves the head one place right, and appends one false bit. The head movement rule gives the new position (`Turing.moveInputPos_pos_of_ne_right`), while appending one false bit changes the output from $t$ zeros to $t+1$ zeros. These are the three asserted properties at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
