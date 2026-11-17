<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallSetCenterOfMass.lean :: FABL.smallSetCenterOfMass_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Fourier coordinate formula

**Claim.** For each coordinate $i$, the $i$th coordinate of the center of mass of $f$ at scale $\alpha$ is the Fourier coefficient of $f$ on $\{i\}$ divided by $\alpha$.

**Proof.** By definition, the $i$th coordinate of the center of mass is the uniform expectation of $f(x)\,\mathrm{signValue}(x_i)$, divided by $\alpha$. The monomial indexed by the singleton $\{i\}$ is exactly $\mathrm{signValue}(x_i)$, since its defining product has one factor. Thus the expectation is the Fourier coefficient at $\{i\}$, giving the asserted equality.
