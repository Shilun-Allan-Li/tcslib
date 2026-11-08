<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/DNF.lean :: Std.Sat.CNF.dual_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of CNF dualization

**Claim.** For every CNF formula $\varphi$, taking its De Morgan dual as a DNF formula and then taking the De Morgan dual of that DNF formula returns $\varphi$.

**Proof.** Dualization preserves the order of the clauses and literals, and changes each literal $(v,b)$ to $(v,\neg b)$. Applying the second dual preserves that order again and negates each Boolean sign once more. Since Boolean negation applied twice returns the original sign, each literal, and therefore each clause and the whole formula, is restored.
