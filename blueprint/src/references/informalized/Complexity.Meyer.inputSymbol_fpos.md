<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.inputSymbol_fpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at a clamped position

**Claim.** If $1\le p\le |y|+1$ and the configuration’s head position is the clamped position $fpos(y,p)$, then its read symbol is $y[p-1]?$.

**Proof.** Apply the fact that a configuration whose head position has value $i+1$ reads the possibly undefined list entry at index $i$ (`inputSymbol_at`), taking $i=p-1$. The lower bound on $p$ makes this index a natural number, and the upper bound ensures that clamping does not change the position: $fpos(y,p)$ has value $p$. Thus the head value is $(p-1)+1$, as required.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
