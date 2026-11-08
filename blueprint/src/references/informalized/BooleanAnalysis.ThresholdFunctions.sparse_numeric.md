<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/SparseSampling.lean :: BooleanAnalysis.ThresholdFunctions.sparse_numeric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound in positive dimension

**Claim.** For every positive integer $n$, $2^{n+1}e^{-2n}<1$.

**Proof.** First, $2<e$, and therefore $4<e^2$. Raising this strict inequality to the positive integer power $n$ gives $4^n<e^{2n}$. Since $n\ge1$, we have $n+1\le2n$, so $2^{n+1}\le2^{2n}=4^n$. Combining these yields $2^{n+1}<e^{2n}$. Dividing by the positive number $e^{2n}$ gives the claim.
