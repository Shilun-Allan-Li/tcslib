<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukGeneratingPolynomial_eq_subset_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generating polynomial as a subset sum

**Claim.** The generating polynomial is the sum over all coordinate subsets $S$ of the monomial $x_S$ times $X^{|S|}$.

**Proof.** Write each factor as $x_iX+1$ and expand the product by choosing one term from each coordinate factor. Each choice is uniquely specified by the subset $S$ of coordinates for which the term $x_iX$ is selected. The resulting term is the product of the signs on $S$, namely $x_S$, multiplied by $X^{|S|}$. Summing over all subsets gives the claimed polynomial identity.
