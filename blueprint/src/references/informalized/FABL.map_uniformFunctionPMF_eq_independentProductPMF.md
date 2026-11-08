<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.map_uniformFunctionPMF_eq_independentProductPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Functions Have Independent Outputs

**Claim.** For finite sets $\iota$, $\alpha$, and $\beta$, with $\alpha$ nonempty, choose a function $a:\iota\to\alpha$ uniformly and send it to the function $i\mapsto\varphi_i(a(i))$. The resulting distribution is the product, over $i\in\iota$, of the distributions obtained by choosing uniformly from $\alpha$ and applying $\varphi_i$.

**Proof.** Compare the probabilities assigned to each target function $y:\iota\to\beta$. By the formula for the independent product distribution (\texttt{independentProductPMF\_apply}), its probability is the product, over coordinates $i$, of the probabilities that a uniform input in $\alpha$ maps under $\varphi_i$ to $y(i)$. Expanding those probabilities expresses the product as a sum over all input functions $a:\iota\to\alpha$; each summand is the uniform probability of $a$ when $y(i)=\varphi_i(a(i))$ for every $i$, and is zero otherwise. This is exactly the probability that a uniformly chosen input function maps to $y$. Indeed, the equality condition either holds at every coordinate or fails at some coordinate, in which case the corresponding product has a zero factor. Hence the two distributions agree at every target function.

**Key facts.** `FABL.independentProductPMF_apply`.
