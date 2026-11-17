<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.uniformLpNorm_sub_toReal_sq_eq_four_mul_relativeHammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Disagreement and Hamming Distance

**Claim.** For Boolean-valued functions $f,g\colon\{-1,1\}^n\to\{-1,1\}$, the squared uniform $2$-norm of the difference of their real sign representations equals four times their relative Hamming distance.

**Proof.** Rewrite the squared uniform $2$-norm as the uniform inner product of the difference with itself (\texttt{uniformLpNorm_two_sq_eq_uniformInner}), and express that inner product as the uniform expectation of the pointwise inner product. Since each sign is either $-1$ or $1$, the squared difference of their real representations is $0$ when the values agree and $4$ when they disagree. Thus the expectation is four times the uniform probability of disagreement. That probability is the relative Hamming distance (\texttt{uniformProbability_ne_eq_relativeHammingDist}), proving the formula.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.uniformProbability_ne_eq_relativeHammingDist`.
