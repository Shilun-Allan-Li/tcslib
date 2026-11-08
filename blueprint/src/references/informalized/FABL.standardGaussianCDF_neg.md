<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianCDF_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF and upper tail

**Claim.** For every real $t$, the standard Gaussian CDF at $-t$ equals the standard Gaussian upper tail at $t$.

**Proof.** By symmetry of the standard Gaussian measure under $x\mapsto -x$, its measure on $(-\infty,-t]$ equals its measure on the preimage of that interval under negation, namely $[t,\infty)$. Since a Gaussian measure assigns zero mass to singletons, the measure of $[t,\infty)$ equals that of $(t,\infty)$. The CDF is the measure of $(-\infty,-t]$, while the upper tail is the measure of $(t,\infty)$ (by the stated upper-tail identity, `standardGaussianUpperTail_eq_measureReal_Ioi`). Thus the two quantities agree.

**Key facts.** `FABL.standardGaussianUpperTail_eq_measureReal_Ioi`.
