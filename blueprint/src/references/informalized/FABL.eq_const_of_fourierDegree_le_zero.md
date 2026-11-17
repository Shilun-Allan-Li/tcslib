<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.eq_const_of_fourierDegree_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier degree zero implies constancy

**Claim.** If a real-valued function on the n-dimensional sign cube has Fourier degree at most zero, then it is constant, with value its Fourier coefficient at the empty set.

**Proof.** Fix an input x and expand f(x) in its Fourier expansion. In the resulting sum, every nonempty set S has positive cardinality, so the degree-zero hypothesis forces its Fourier coefficient to vanish (the characterization of degree bounds by vanishing coefficients above that degree, `FABL.fourierDegree_le_iff`). Thus only the term indexed by the empty set remains. The monomial for the empty set is the empty product, equal to 1, so the sum is exactly the empty-set Fourier coefficient, independently of x.

**Key facts.** `FABL.fourier_expansion`, `FABL.fourierDegree_le_iff`.
