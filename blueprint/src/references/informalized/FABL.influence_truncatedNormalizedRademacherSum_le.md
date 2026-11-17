<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.influence_truncatedNormalizedRademacherSum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound for a Truncated Sum

**Claim.** For positive $n$ and every coordinate $i$, the influence of the truncated normalized Rademacher sum is at most $1/n$.

**Proof.** Fix positive $n$ and a coordinate $i$. The pointwise bound on the absolute discrete derivative of the truncated sum gives $|D_i g(x)|\le (\sqrt n)^{-1}$ for every input (`FABL.abs_discreteDerivative_truncatedNormalizedRademacherSum_le`). Squaring preserves this inequality because both sides are nonnegative, so the squared derivative is at most $(\sqrt n)^{-2}$. Averaging this pointwise bound over the cube bounds the influence by the same constant. Finally, $(\sqrt n)^{-2}=1/n$, since $n>0$ and hence $(\sqrt n)^2=n$.

**Key facts.** `FABL.abs_discreteDerivative_truncatedNormalizedRademacherSum_le`.
