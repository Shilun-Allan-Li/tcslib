<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading an Interior Input Position

**Claim.** For a configuration on input $x$ with control state $q$, head position $i+1$, and output $o$, where $i\le |x|$, the read symbol is the $i$th bit when $i<|x|$, and no symbol when $i=|x|$.

**Proof.** The configuration's head position has value $i+1$. The input-position rule says that at this position the read symbol is the option-valued list entry $x[i]?$. This is the $i$th bit when it exists, and none at the right end of the input.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
