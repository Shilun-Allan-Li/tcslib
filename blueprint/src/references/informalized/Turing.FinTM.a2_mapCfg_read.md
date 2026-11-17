<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at an indexed position

**Claim.** In the specified mapping-machine configuration, whose input head is at position $i+1$, the symbol under the head is $x[i]?$, which is the $i$th symbol of $x$ when $i<|x|$ and blank when $i=|x|$.

**Proof.** The input-symbol-at-position fact says that any configuration on input $x$ whose input-head position is $i+1$ reads $x[i]?$. The constructed configuration has precisely that head position, so the result follows directly (`inputSymbol_at`).

**Key facts.** `Turing.FinTM.inputSymbol_at`.
