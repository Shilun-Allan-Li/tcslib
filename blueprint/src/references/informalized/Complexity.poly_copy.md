<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Input-Copying Phase

**Claim.** For every $i\le |x|$, after $i$ steps from the initial configuration, the machine is in the copy state with input head at position $i$, every work tape containing $1^i$, every work head at $i$, and empty output.

**Proof.** Proceed by induction on $i$. At $i=0$, the initial configuration has the copy state, input head at position $0$, blank work tapes, heads at $0$, and empty output; these are exactly the claimed contents for $1^0$. For the successor step, assume the description holds at $i$ and use the run decomposition that expresses the next configuration as one step after the first $i$ steps. Since $i<|x|$, the input head reads $x_i$. The copy transition writes a $1$ at each work head's current cell $i$, moves each work head one cell right, and advances the input head; it remains in the copy state and emits nothing. Writing at cell $i$ extends the tape from $1^i$ to $1^{i+1}$ (`polyTape_write`), and the input-head position update gives $i+1$. Thus all parts of the claimed configuration hold at $i+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.polyTape_write`.
