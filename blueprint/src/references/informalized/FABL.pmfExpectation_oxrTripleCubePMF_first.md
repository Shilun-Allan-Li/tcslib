<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrTripleCubePMF_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-query expectation and constant coefficient

**Claim.** For the coordinatewise mixture of pair and parity triple constructions, the expectation of $f$ evaluated at the first query vector equals the Fourier coefficient of $f$ at the empty set.

**Proof.** At each query vector, expand $f$ in its Fourier basis (`fourier_expansion`). Taking expectation term by term is valid for this finite sum (`pmfExpectation_sum`). For each term, factor out its Fourier coefficient using constant scaling of expectation (`pmfExpectation_const_mul`). The remaining expectation is that of the first-query monomial; it can be written as the product of this monomial with the empty-set monomials on the second and third queries, since those monomials equal $1$. The triple-cube monomial expectation formula (`pmfExpectation_oxrTripleCubePMF_monomials`), applied with $B=C=\varnothing$, says this expectation is $1$ when $S\subseteq\varnothing$ and zero otherwise. Thus only $S=\varnothing$ contributes to the Fourier sum, leaving $\widehat f(\varnothing)$.

**Key facts.** `FABL.fourier_expansion`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_oxrTripleCubePMF_monomials`.
