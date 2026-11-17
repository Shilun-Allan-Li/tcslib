<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.sv_sgn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Coordinates for Symbolic Answers

**Claim.** For every selector, time $t<2^W$, sign $s$, and natural number $a$, the symbolic answer at $(t,a)$ equals the answer at signed coordinate $(-1)^s a$.

**Proof.** Unfold the signed-coordinate and signed-integer conventions and split on the Boolean sign. When the sign is false, the signed coordinate is the nonnegative integer $a$, so its sign test is false and its natural-number magnitude is $a$; the two expressions agree directly. When the sign is true and $a>0$, the signed coordinate is $-a$, whose sign is negative and whose magnitude is $a$, again giving the same symbolic answer. When the sign is true and $a=0$, both signed conventions produce zero; equality of the two sign-indexed symbolic answers at zero is exactly the symmetric-zero result (`Complexity.Meyer.sv_negZero`).

**Key facts.** `Complexity.Meyer.sv_negZero`.
