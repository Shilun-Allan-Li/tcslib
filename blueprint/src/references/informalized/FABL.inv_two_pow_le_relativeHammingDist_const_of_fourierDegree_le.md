<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.inv_two_pow_le_relativeHammingDist_const_of_fourierDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance from a Constant

**Claim.** If a Boolean function on the sign cube is nonconstant and has Fourier degree at most $k$, then it differs from any fixed constant sign on at least a fraction $2^{-k}$ of inputs.

**Proof.** Subtract the constant sign value from the real-valued embedding, defining $g(x)=f(x)-	ext{signValue}(c)$. This function is nonzero: if it vanished everywhere, injectivity of the sign embedding would imply $f(x)=c$ for every input, contradicting nonconstancy. Subtracting a constant does not increase Fourier degree (the degree bound for subtracting a constant, `fourierDegree_sub_const_le`), so the nonzero-function lower bound gives $2^{-k}\leq \Pr[g(x)\ne 0]$ (`inv_two_pow_le_uniformProbability_ne_zero_of_fourierDegree_le`). Since the function takes only the two sign values, $g(x)\ne 0$ exactly when $f(x)\ne c$; injectivity of the sign embedding ensures these conditions agree. Finally, the uniform probability of disagreement equals the relative Hamming distance (`uniformProbability_ne_eq_relativeHammingDist`).

**Key facts.** `FABL.fourierDegree_sub_const_le`, `FABL.inv_two_pow_le_uniformProbability_ne_zero_of_fourierDegree_le`, `FABL.signValue_injective`, `FABL.uniformProbability_ne_eq_relativeHammingDist`.
