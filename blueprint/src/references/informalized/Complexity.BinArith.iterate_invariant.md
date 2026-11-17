<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.iterate_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation under iteration

**Claim.** If a property $I$ is preserved by a function $g$, then whenever $I(s)$ holds, it also holds after applying $g$ to $s$ any natural number of times.

**Proof.** Induct on the number of iterations. At zero, the result is $s$, so the property is the hypothesis $I(s)$. For the successor case, the induction hypothesis gives the property after the current number of iterations. One further application of $g$ preserves it by the assumed implication $I(x)\Rightarrow I(g(x))$.
