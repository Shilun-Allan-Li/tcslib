<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.productProbabilityPMF_hasFullSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full support of the product distribution

**Claim.** If $\pi$ assigns positive mass to every element of the finite set $\Omega$, then its product distribution assigns positive mass to every $n$-tuple.

**Proof.** Fix a function $x:\mathrm{Fin}(n)\to\Omega$. Its product-distribution mass is $\prod_i\pi(x_i)$ (\texttt{productProbabilityPMF\_apply}). Each factor is nonzero by the full-support hypothesis applied to $x_i$. A finite product is nonzero exactly when each of its factors is nonzero, so the mass at $x$ is nonzero. Since $x$ was arbitrary, the product distribution has full support.

**Key facts.** `FABL.productProbabilityPMF_apply`.
