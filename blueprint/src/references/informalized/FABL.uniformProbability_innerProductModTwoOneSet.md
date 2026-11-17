<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.uniformProbability_innerProductModTwoOneSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity of a Uniform Binary Inner Product

**Claim.** For every $m\in\mathbb N$, if $u,v$ are chosen independently and uniformly from $\mathbb F_2^m$, the probability that their dot product is $1$ is $\frac{1-2^{-m}}{2}$.

**Proof.** Membership in the specified event means that the binary inner product is $1$. Every element of $\mathbb F_2$ is either $0$ or $1$ (\texttt{f\u2082\_eq\_zero\_or\_one}), so the event's indicator agrees at every input with the real-valued embedding of that inner product. The expected value of this embedding over the paired uniform vectors is $(1-(2^m)^{-1})/2$ (\texttt{expect\_booleanRealEmbedding\_innerProductModTwoBit}), which is exactly the event's uniform probability.

**Key facts.** `FABL.f₂_eq_zero_or_one`, `FABL.expect_booleanRealEmbedding_innerProductModTwoBit`.
