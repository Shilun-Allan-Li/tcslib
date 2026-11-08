<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.monomial_insert_zero_tailFrequency_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial on a prefixed sign assignment

**Claim.** For a sign assignment prefixed by $b$, the monomial on coordinate $0$ together with the shifted coordinates of $S$ equals the sign represented by $b$ times the monomial on $S$.

**Proof.** Coordinate $0$ is not among the shifted coordinates, so the product over their union splits into the factor at $0$ and the product over the shifted set (`zero_notMem_tailFrequency`). The value at coordinate $0$ of the prefixed assignment is $b$, giving the factor $\operatorname{signValue}(b)$. The monomial over the shifted coordinates is the original monomial on $S$ evaluated at $x$ (`monomial_tailFrequency_fin_cons`). Multiplying these factors proves the identity.

**Key facts.** `FABL.zero_notMem_tailFrequency`, `FABL.monomial_tailFrequency_fin_cons`.
