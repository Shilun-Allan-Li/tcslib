<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.fin3_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cases for three indices

**Claim.** If a predicate on $\mathrm{Fin}(3)$ holds at $0$, $1$, and $2$, then it holds at every element of $\mathrm{Fin}(3)$.

**Proof.** Every element of $\mathrm{Fin}(3)$ has a natural-number value less than $3$, so its value is one of $0$, $1$, or $2$. In the respective cases, the corresponding hypothesis supplies the predicate.
