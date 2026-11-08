<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.three_quarters_pow_five_mul_le_quarter_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Power Comparison

**Claim.** For every natural number $k$, $(3/4)^{5k}\le(1/4)^k$.

**Proof.** Rewrite the left side as $((3/4)^5)^k$. Since $(3/4)^5=243/1024\le1/4$, raising both nonnegative sides to the natural power $k$ preserves the inequality, giving $((3/4)^5)^k\le(1/4)^k$.
