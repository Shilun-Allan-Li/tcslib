<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.pmfExpectation_sq_sub_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Sign-Valued Random Variable

**Claim.** For a function taking only the values $-1$ and $1$, the expected squared deviation from its mean equals four times the product of the probabilities of the two sign values.

**Proof.** Apply the absolute-deviation formula (`pmfExpectation_abs_sub_mean_rpow`) with exponent $2$. Since squaring removes the absolute value, it expresses the desired expectation as $a(2b)^2+b(2a)^2$, where $a$ and $b$ are the plus and minus masses. Expanding and factoring gives $4ab(a+b)$. The two masses sum to $1$ (`pmfSignPlusMass_add_minus`), so this simplifies to $4ab$, as claimed.

**Key facts.** `FABL.pmfExpectation_abs_sub_mean_rpow`, `FABL.pmfSignPlusMass_add_minus`.
