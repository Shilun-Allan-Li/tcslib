<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Int.natCast_toNat_emod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer Remainder as a Natural

**Claim.** For positive $M$ and any integer $x$, the remainder of $x$ modulo $M$, converted to a natural number and then back to an integer, is the original remainder.

**Proof.** Since $M>0$, its integer cast is nonzero. The integer remainder modulo a positive modulus is nonnegative, so the remainder equals the integer cast of its natural-number value. This is the standard characterization of converting a nonnegative integer to a natural number and back.
