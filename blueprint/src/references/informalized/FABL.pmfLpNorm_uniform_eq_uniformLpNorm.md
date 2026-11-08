<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfLpNorm_uniform_eq_uniformLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Norm Agreement

**Claim.** For a finite nonempty set $\Omega$, a real number $p$, and $f:\Omega\to\mathbb{R}$, the $L^p$ norm under the uniform probability mass function equals the uniform $L^p$ norm of $f$.

**Proof.** Unfold both norm definitions. The expressions then have the same outer power, and their inner expectations agree by the fact that expectation under the uniform probability mass function is uniform expectation ($\texttt{FABL.pmfExpectation_uniformPMF_eq_expect}$), applied to $x\mapsto |f(x)|^p$.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
