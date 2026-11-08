<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.pmfExpectation_affine_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Moments by the Binomial Formula

**Claim.** For a probability mass function on a finite set and a real-valued function $X$, the expectation of $(a+cX)^m$ is $\sum_{j=0}^{m}\binom{m}{j}a^{m-j}c^j\mathbb E_{\mathrm{law}}[X^j]$.

**Proof.** Expand each value $(a+cX(x))^m$ by the binomial theorem, after commuting the two summands to write it as $(cX(x)+a)^m$. In the finite weighted sum defining expectation, distribute the sum over the binomial terms and interchange the finite sums over the index $j$ and outcomes $x$. For each fixed $j$, the factors independent of $x$ can be taken outside the expectation; the remaining weighted sum is $\mathbb E_{\mathrm{law}}[X^j]$. Since $1^{m-j}=1$, this yields exactly the claimed formula.
