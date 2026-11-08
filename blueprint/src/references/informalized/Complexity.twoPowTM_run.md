<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.twoPowTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Unary-Output Machine

**Claim.** For each binary word $x$ and each $i\le |x|$, after $i$ steps the machine is in its unique state, its input head is at position $i+1$, and its output is a string of $i$ zeros.

**Proof.** Induct on $i$. At zero steps the initial configuration has the unique state, head position $1$, and empty output, which is the list of zero zeros. For the successor step, use the induction hypothesis at time $i$. Since $i<|x|$, the input-symbol rule identifies the scanned symbol as $x[i]$ (\texttt{inputSymbolInner}). The machine’s transition emits one zero and remains in its unique state. Its rightward move advances the head from $i+1$ to $i+2$ (\texttt{moveInputPos\_pos\_of\_ne\_right}); the output is the previous string of $i$ zeros followed by one more zero. This is precisely the string of $i+1$ zeros.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
