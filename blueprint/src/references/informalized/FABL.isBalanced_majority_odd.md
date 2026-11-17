<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.isBalanced_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balance of odd-arity majority

**Claim.** For every natural number $m$, majority on $2m+1$ inputs is balanced under the uniform distribution.

**Proof.** Balance is equivalent to the vanishing of the Fourier coefficient at the empty set (`isBalanced_iff_fourierCoeff_empty_eq_zero`). Apply the odd-arity majority coefficient result to the empty set: the arity $2m+1$ is odd, and the empty set has even cardinality. Thus this Fourier coefficient is zero, proving balance.

**Key facts.** `FABL.isBalanced_iff_fourierCoeff_empty_eq_zero`, `FABL.fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card`.
