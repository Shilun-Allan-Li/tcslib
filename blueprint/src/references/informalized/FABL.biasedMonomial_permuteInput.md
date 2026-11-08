<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.biasedMonomial_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation Equivariance of Biased Monomials

**Claim.** Permuting the input coordinates by $\sigma$ and evaluating the biased monomial indexed by $S$ gives the same value as evaluating at the original input the biased monomial indexed by $\sigma(S)$.

**Proof.** Write each biased monomial as the product of standardized biased signs over its indexing set, using the biased monomial evaluation formula (\texttt{FABL.biasedMonomial_apply}). Under the input permutation, the factor at coordinate $i$ becomes the factor at coordinate $\sigma(i)$. Reindexing the finite product by the permutation therefore gives the product over $\sigma(S)$ at the original input, which is the biased monomial indexed by $\sigma(S)$.

**Key facts.** `FABL.biasedMonomial_apply`.
