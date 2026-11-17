<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.basisExpandedSmallBiasPolynomial_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial evaluation identity

**Claim.** Evaluating the basis-expanded polynomial at $r$ gives the field-pairing coefficient of the basis-expanded family at $r$.

**Proof.** Evaluating the polynomial term by term gives the sum over $i$ of the grouped coefficient in block $i$ multiplied by $r^{i+1}$. Expand each grouped coefficient as the sum over $j$ of $\gamma(i,j)$ times the $j$th basis vector (\(\texttt{basisExpandedGroupedCoefficient\_eq\_sum}\)). Distributing multiplication over this sum yields a double sum whose $(i,j)$ term is $\gamma(i,j)$ times the basis vector multiplied by $r^{i+1}$. Reindex the pairs $(i,j)$ by the coordinates $q$ of the $n\ell$-cube. By the definition of the basis-expanded family, each such term is precisely $\gamma(q)$ times that family's value at $q$. Summing over $q$ is the definition of the field-pairing coefficient, which proves the identity.

**Key facts.** `FABL.basisExpandedGroupedCoefficient_eq_sum`.
