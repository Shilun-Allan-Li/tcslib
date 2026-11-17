<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrTripleCubePMF_tripleProduct_fourier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Formula for the Triple Product

**Claim.** For any real-valued function $f$ on the sign cube, the expected product of its values on the three query vectors equals the stated double Fourier sum over $S$ and its subsets.

**Proof.** Expand each of the three copies of $f$ in its Fourier basis (`fourier_expansion`). Distribute the products over the finite sums; linearity of expectation (`pmfExpectation_sum`) and extraction of constant factors (`pmfExpectation_const_mul`) turn the result into a triple sum of Fourier coefficients times the expected product of three monomials. The monomial expectation formula (`pmfExpectation_oxrTripleCubePMF_monomials`) says this expectation vanishes unless the second and third index sets agree and the first is contained in them. Summing over the third index therefore leaves, for each pair $A\subseteq B$, the factor $(-(1-\delta))^{|A|}(-\delta)^{|B|-|A|}$. Finally swap the order of the finite sums and rename the containing set $S$ and its subset $J$; this is exactly the displayed double sum.

**Key facts.** `FABL.fourier_expansion`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_oxrTripleCubePMF_monomials`.
