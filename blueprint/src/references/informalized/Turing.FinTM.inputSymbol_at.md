<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.inputSymbol_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at a specified position

**Claim.** If the input head is at position $i+1$ and $i\le |x|$, then the scanned symbol is $x[i]?$.

**Proof.** Split according to whether $i<|x|$. In that case, the input head is at the position corresponding to the $i$-th input cell, so the input-symbol formula for an interior position gives `some x[i]` (`Turing.inputSymbolInner`). Since the list lookup is in bounds, this equals the optional lookup $x[i]?$. If $i$ is not less than the length, the hypothesis $i\le |x|$ forces $i=|x|$. The head is then at position $|x|+1$, the right-end boundary, where the configuration's input-symbol definition returns `none`; the optional lookup at the end is also `none`.

**Key facts.** `Turing.inputSymbolInner`.
