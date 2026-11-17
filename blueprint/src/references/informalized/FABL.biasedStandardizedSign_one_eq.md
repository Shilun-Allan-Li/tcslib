<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedStandardizedSign_one_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standardized Sign at One

**Claim.** For every real bias parameter $p$, the standardized sign evaluated at $1$ equals $2p/\mathrm{biasSigma}(p)$.

**Proof.** At the sign value $1$, the numerator in the standardized expression is $1-(1-2p)=2p$. Dividing by the scale $\mathrm{biasSigma}(p)$ gives the claimed identity.
