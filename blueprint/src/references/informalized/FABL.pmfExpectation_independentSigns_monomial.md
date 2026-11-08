<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_independentSigns_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Monomial Expectation

**Claim.** For independent signs with coordinate means $\mu_i$, the expectation of the monomial indexed by $S$ is $\prod_{i\in S}\mu_i$.

**Proof.** For each coordinate $i$, define a function equal to the sign itself when $i\in S$ and equal to $1$ otherwise. The product of these coordinate functions is the monomial indexed by $S$. The independent-product expectation identity (\texttt{FABL.pmfExpectation\_independentProductPMF\_prod}) expresses its expectation as the product of the individual coordinate expectations. For indices in $S$, the sign law has mean $\mu_i$ (\texttt{FABL.pmfExpectation\_signPMFOfMean}); outside $S$, the coordinate function is constant one, whose expectation is one (\texttt{FABL.pmfExpectation\_const\_one}). The product therefore reduces to $\prod_{i\in S}\mu_i$.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_signPMFOfMean`, `FABL.pmfExpectation_const_one`.
