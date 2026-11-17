<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.sv_negZero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric Answers at Zero

**Claim.** For every tape selector and every $t<2^W$, the two symbol queries distinguished by the Boolean sign parameter have equal encoded answers at coordinates $(t,0)$.

**Proof.** Apply the checker hypothesis at $(t,0,0)$, once to the zero-index condition with sign true and once with sign false. The time and index bounds hold, and the resulting checker equalities state that the two sign choices give the same answer bit for each of the two symbol-bit queries. Since the symbolic answer at zero is formed from those two bits by the same rule for either sign, the resulting optional Boolean values are equal.

**Key facts.** `Complexity.Meyer.NumVal_ans`.
