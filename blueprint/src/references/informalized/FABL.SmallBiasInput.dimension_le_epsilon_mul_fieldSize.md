<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.dimension_le_epsilon_mul_fieldSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension Bound by Field Size

**Claim.** For a small-bias input with dimension $n$, bias parameter $\epsilon$, and field degree $r$, the real inequality $n\leq \epsilon 2^r$ holds.

**Proof.** First, the denominator is positive: the positive numerator makes twice the numerator positive, and twice the numerator is at most the denominator. By the defining property of the ceiling quotient, $n$ times the denominator is at most the numerator times the scale. The scale is at most $2^r$ (`SmallBiasInput.scale_le_fieldSize`), so multiplying this bound by the nonnegative numerator gives $n$ times the denominator at most the numerator times $2^r$. Cast this inequality to the reals. Since the real denominator is positive, division by it preserves the inequality; rewriting the quotient as $\epsilon 2^r$ proves the claim.

**Key facts.** `FABL.SmallBiasInput.scale_le_fieldSize`.
