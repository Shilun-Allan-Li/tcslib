<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_good_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on valid code and clock fields

**Claim.** If a bit string $z$ satisfies the validity guard, then its code field and clock field each have length at most $|z|$.

**Proof.** The validity specification (Complexity.tmsat_good_spec) decomposes $z$ as the concatenation of its instance part and certificate part, and identifies the instance part as the encoded quadruple of the code, input, width, and clock fields. The quadruple length bounds (Complexity.tmsat_quad_bounds) imply that both the code length and the clock-field length are at most the length of that instance part. Since the certificate part has nonnegative length, the instance part is no longer than $z$. Combining these inequalities gives both claimed bounds.

**Key facts.** `Complexity.tmsat_good_spec`, `Complexity.tmsat_quad_bounds`.
