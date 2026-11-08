<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.length_pairLayout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Pair Layout

**Claim.** The pair layout formed from the first $n$ input bits twice, the constants $0$ and $1$, and the next $a$ input bits has length $2n+2+a$.

**Proof.** Each of the first $n$ indices contributes a two-element list, so their flattened list has length $n\cdot2$ by the constant-length flat-map formula (`Complexity.CfgTableau.length_flatMap_const`). Appending the two constants adds $2$, and mapping the next $a$ indices to single input sources adds $a$. The total is $2n+2+a$.

**Key facts.** `Complexity.CfgTableau.length_flatMap_const`.
