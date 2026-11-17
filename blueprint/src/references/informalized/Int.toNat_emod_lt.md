<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Int.toNat_emod_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Natural Remainder

**Claim.** For positive $M$ and any integer $x$, the natural-number value of the remainder of $x$ modulo $M$ is strictly less than $M$.

**Proof.** The integer remainder modulo the positive integer cast of $M$ is strictly less than that modulus. Since the remainder is nonnegative, passing to its natural-number value preserves the bound; thus it is less than $M.
