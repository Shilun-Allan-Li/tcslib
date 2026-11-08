<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTail_eq_measureReal_Ioi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail as a Measure

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $t$ equals the standard Gaussian measure of $(t,\infty)$.

**Proof.** The upper tail is one minus the Gaussian cumulative distribution function at $t$. The cumulative distribution function is the probability of $(-\infty,t]$. For this measurable set, the probability of its complement is one minus its probability; its complement is precisely $(t,\infty)$. Taking real-valued probabilities gives the claimed identity.
