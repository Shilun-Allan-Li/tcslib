<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.monomial_binaryCubeSignEquiv_eq_numerical_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary monomial expansion

**Claim.** After encoding each bit as a sign, the monomial on $S$ equals the sum over all subsets $T\subseteq S$ of $(-2)^{|T|}$ times the indicator that every bit on $T$ is $1$.

**Proof.** For each coordinate $i\in S$, the encoded sign is $1-2\mathbf{1}_{\{x_i=1\}}$; this is the coordinate identity supplied by `signValue_binaryCubeSignEquiv_eq_one_sub_two`. Thus the monomial is a product over $S$ of factors of the form $1+a_i$, where $a_i=-2\mathbf{1}_{\{x_i=1\}}$. Distributing this product amounts to choosing, for each factor, either $1$ or $a_i$, and hence gives one term for each subset $T$ of chosen coordinates. The term for $T$ is the product of the $a_i$ over $T$, with the unchosen factors contributing $1$. Factoring out $(-2)^{|T|}$ leaves the product of the bit indicators over $T$, which is exactly the numerical monomial in the claim. The empty choice contributes $1$.

**Key facts.** `FABL.signValue_binaryCubeSignEquiv_eq_one_sub_two`.
