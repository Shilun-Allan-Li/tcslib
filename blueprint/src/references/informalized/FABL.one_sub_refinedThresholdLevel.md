<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.one_sub_refinedThresholdLevel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement of the refined threshold level

**Claim.** For every real number $\tau>0$, $1-\mathrm{refinedThresholdLevel}(\tau)=\frac{1}{1+\tau}$.

**Proof.** Substitute $\mathrm{refinedThresholdLevel}(\tau)=\tau/(1+\tau)$. Since $\tau>0$, the denominator is nonzero. Bringing the terms on the left over a common denominator gives $(1+\tau-\tau)/(1+\tau)=1/(1+\tau)$, as required.
