<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperTail_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Gaussian Upper Tail

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $t$ is strictly positive.

**Proof.** Strict increase of the standard Gaussian CDF gives $\operatorname{CDF}(t)<\operatorname{CDF}(t+1)$, since $t<t+1$. The CDF is at most $1$ at every real argument, so in particular $\operatorname{CDF}(t+1)\le 1$. Hence $\operatorname{CDF}(t)<1$, and subtracting from $1$ shows that the upper-tail probability at $t$ is positive.

**Key facts.** `FABL.strictMono_standardGaussianCDF`.
