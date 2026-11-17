<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaSeedLength.lean :: FABL.exists_violaSmallBiasDistribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A small-bias fooling distribution

**Claim.** For the stated positive parameters, there is a small-bias generator whose $d$-fold convolution fools the degree-$d$ polynomial sign class within error $\varepsilon$, with seed bits bounded as claimed.

**Proof.** Choose the base bias parameter $\eta=\operatorname{violaBaseBias}(\varepsilon,d)$. The supplied bounds ensure $0<\eta\le1/2$ (`violaBaseBias_pos`, `violaBaseBias_le_half`). Since $n\ge1$, the real-parameter small-bias generator theorem (`exists_smallBiasGenerator_of_real`) gives a nonzero extension-field dimension $\ell$ such that its generator density is $\eta$-biased and its generating multiset has size at most $16(n/\eta)^2$. Applying the convolution fooling theorem (`ProbabilityDensity.IsBiased.violaTheorem`) with this bias and degree gives fooling error $\operatorname{violaError}(\eta,d)$. By the base-bias identity (`violaError_baseBias`), this error is exactly $\varepsilon$. Finally, the multiset-size bound implies the asserted seed-bit bound by `violaSmallBiasSeedBits_le_of_card`.

**Key facts.** `FABL.violaBaseBias_pos`, `FABL.violaBaseBias_le_half`, `FABL.exists_smallBiasGenerator_of_real`, `FABL.ProbabilityDensity.IsBiased.violaTheorem`, `FABL.violaError_baseBias`, `FABL.violaSmallBiasSeedBits_le_of_card`.
