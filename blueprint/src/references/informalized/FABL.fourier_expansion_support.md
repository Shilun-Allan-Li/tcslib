<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HomogeneousMoments.lean :: FABL.fourier_expansion_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier expansion on its support

**Claim.** The function equals the sum of its Fourier terms over precisely the subsets whose Fourier coefficients are nonzero.

**Proof.** The full Fourier expansion expresses $f(x)$ as the sum over all subsets $S$ of $\widehat f(S)\chi_S(x)$ (the Fourier expansion theorem, `fourier_expansion`). Restrict this finite sum to the Fourier support, which consists of those $S$ with nonzero coefficient. Every omitted term has coefficient zero and therefore contributes zero. The restricted sum is consequently unchanged.

**Key facts.** `FABL.fourier_expansion`.
