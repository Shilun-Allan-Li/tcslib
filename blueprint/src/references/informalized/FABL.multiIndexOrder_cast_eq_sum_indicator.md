<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.multiIndexOrder_cast_eq_sum_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multi-index order as an indicator sum

**Claim.** The number of coordinates where a multi-index $a$ differs from the distinguished element $z$, viewed as a real number, equals the sum of the indicators of those coordinate inequalities.

**Proof.** The support of $a$ is the finite set of positions $i$ for which $a(i)\ne z$, and its order is the cardinality of this set. The cardinality, viewed as a real number, is the sum of $1$ over the support. Rewriting this as a sum over all positions, with summand $1$ on the support and $0$ elsewhere, gives exactly $\sum_i\mathbf 1_{a(i)\ne z}$.
