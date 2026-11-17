<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.computableDAG_real_cutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real and Natural Cutoffs

**Claim.** For every number of input bits, the Boolean functions computable by a fan-in-two circuit whose size as a real number is at most the stated real cutoff are exactly those computable with size at most the corresponding natural-number quotient.

**Proof.** First prove that, for every natural size $k$, the real inequality $k\le 2^n/(10n)$ is equivalent to the natural inequality $k\le 2^n/(10n)$, where the latter quotient is taken in the natural numbers. If $n=0$, both conditions reduce to $k=0$. If $n>0$, the denominator is positive, so clearing it turns the real inequality into $10nk\le 2^n$; the natural division criterion turns the natural inequality into the same condition. Now expand membership in each of the two sets of functions. Both require the same circuit properties and the same represented function, and the size conditions are equivalent by the established cutoff equivalence. Hence the two sets are equal.
