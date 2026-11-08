<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelationDistillation.lean :: FABL.independentSignPair_monomial_right_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A sign monomial correlation

**Claim.** Under the stated coordinatewise mean assumptions, the expectation of the product of the left signs indexed by $S$ and the right sign at $i$ is $\rho_i$ when $S=\{i\}$ and zero otherwise.

**Proof.** For each coordinate $j$, combine the factors involving its pair of signs into one function: include the left sign if $j\in S$, include the right sign if $j=i$, and use $1$ for either missing factor. The product over coordinates of these functions is exactly the random quantity in question. The expectation-of-products formula for independent products (\texttt{FABL.pmfExpectation_independentProductPMF_prod}) therefore expresses its expectation as the product of the coordinate expectations. At a coordinate with both signs present, that expectation is $\rho_i$ when $j=i$, by the assumed product mean. With only a left or only a right sign present, it is zero by the respective mean-zero hypothesis. With neither present it is one, since the function is constant one (\texttt{FABL.pmfExpectation_const_one}). If $S=\{i\}$, only coordinate $i$ has both signs present and all other factors are one, so the product is $\rho_i$. If $i\notin S$, the right-sign factor at $i$ has mean zero. If $i\in S$ but $S\ne\{i\}$, some other coordinate in $S$ has only its left sign, giving a zero factor. In either remaining case the total product is zero.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_prod`, `FABL.pmfExpectation_const_one`.
