<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.selectorRetention_retentionCorrelation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retention Parameter Inversion

**Claim.** For every real number $\rho$, applying the selector-retention function to the retention correlation $2\rho-1$ returns $\rho$.

**Proof.** Substituting the retention correlation into the selector-retention formula gives $\bigl(1+(2\rho-1)\bigr)/2$. Simplifying the numerator yields $2\rho$, and division by $2$ gives $\rho$.
