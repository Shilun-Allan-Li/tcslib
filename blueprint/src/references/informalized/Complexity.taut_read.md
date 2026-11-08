<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at an indexed configuration

**Claim.** In the configuration indexed by $i$, the input symbol is the $i$-th symbol of $x$, or none when $i=|x|$.

**Proof.** The configuration's input-head position has value $i+1$. The input-symbol characterization for a head at that encoded position states that the symbol read is $x[i]?$, the optional $i$-th list entry (`Turing.FinTM.inputSymbol_at`). Applying it to this configuration gives the result.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
