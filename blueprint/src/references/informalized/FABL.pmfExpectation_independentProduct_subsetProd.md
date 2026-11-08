<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_independentProduct_subsetProd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Subset Product

**Claim.** For any subset $S$ of a finite index set, the expectation under independent sampling of the product of the functions indexed by $S$ equals the product of their individual expectations over $S$.

**Proof.** Extend each coordinate function to all indices by setting $q'_i=q_i$ on $S$ and $q'_i=1$ outside $S$. Then the product over all indices of $q'_i(X_i)$ equals the original product over $S$. For each coordinate, its expectation is the expectation of $q_i$ if $i\in S$, and is $1$ otherwise; in the latter case this uses that the expectation of the constant-one function is one (\texttt{FABL.pmfExpectation\_const\_one}). Apply the product-expectation identity for independent coordinate functions (\texttt{FABL.pmfExpectation\_independentProductPMF\_prod}) to the extended family. The resulting product over all indices has exactly the desired factors on $S$, with only unit factors elsewhere, proving the claim.

**Key facts.** `FABL.pmfExpectation_const_one`, `FABL.pmfExpectation_independentProductPMF_prod`.
