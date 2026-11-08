<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.normalizedMargin_eq_linearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Margin as a Linear Form

**Claim.** For every natural number $n$ and sign vector $x$, the normalized coordinate sum $(\sqrt n)^{-1}\sum_i x_i$ is the linear form whose coefficients are all $(\sqrt n)^{-1}$.

**Proof.** By definition, the linear form with constant coefficient $(\sqrt n)^{-1}$ is $\sum_i (\sqrt n)^{-1}\operatorname{signValue}(x_i)$. Distributing the common scalar across the finite sum gives $(\sqrt n)^{-1}\sum_i\operatorname{signValue}(x_i)$, as required.
