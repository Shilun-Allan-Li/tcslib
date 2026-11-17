<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThree_eq_multilinearPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multilinear expansion

**Claim.** The mod-three indicator is the multilinear polynomial with coefficients given by the stated formula: a constant contribution of $1/3$ for the empty set and, for even-cardinality sets, the additional term $\frac23(-\frac12)^n(-1)^{(|S|\bmod 4)/2}(\sqrt3)^{|S|}$; odd-cardinality sets contribute zero.

**Proof.** Begin with the Fourier expansion, which expresses the indicator as $1/3$ plus $\frac23(-1/2)^n$ times a sum over even-cardinality subsets. Rewrite the multilinear polynomial by distributing its coefficient formula across the sum over all subsets. The part supported on the empty set contributes exactly $1/3$, since the monomial of the empty set is $1$. In the remaining part, only even-cardinality subsets survive; factor out the common scalar $\frac23(-1/2)^n$ and rewrite the restricted sum as a sum over those subsets. Its summand is precisely the weight in the Fourier expansion multiplied by the subset monomial. Thus the polynomial and the Fourier expansion coincide.

**Key facts.** `FABL.modThree_fourier_expansion`.
