<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.toNat_natCast_add_natCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural casts and truncated addition

**Claim.** For natural numbers $a,b$, converting their sum as integers to a natural number gives $a+b$.

**Proof.** The integer cast preserves addition, so $a+b$ viewed in the integers is the cast of the natural sum. The natural number obtained from the cast of a natural number by integer-to-natural conversion is that original natural number. Applying these two facts gives the equality.
