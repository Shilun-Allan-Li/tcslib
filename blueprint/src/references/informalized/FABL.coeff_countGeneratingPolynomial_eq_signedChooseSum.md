<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.coeff_countGeneratingPolynomial_eq_signedChooseSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Binomial Coefficient Formula

**Claim.** The coefficient of $X^j$ in $(1-X)^z(1+X)^{n-z}$ is $\sum_{k=0}^{j}(-1)^k\binom{z}{k}\binom{n-z}{j-k}$.

**Proof.** The coefficient of degree $j$ in a product is the sum over pairs of degrees whose sum is $j$. Reindex those pairs by the degree $k$ contributed by $(1-X)^z$, so the other factor contributes degree $j-k$. The coefficient formulas for the two binomial powers give respectively $(-1)^k\binom{z}{k}$ and $\binom{n-z}{j-k}$; multiplying and summing over $0\leq k\leq j$ yields the formula. The first factor's formula is the signed binomial coefficient identity (\texttt{coeff\_one\_sub\_X\_pow}).

**Key facts.** `FABL.coeff_one_sub_X_pow`.
