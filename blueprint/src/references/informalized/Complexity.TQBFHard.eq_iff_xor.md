<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.eq_iff_xor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality Detected by XOR

**Claim.** Two finite bit strings are equal exactly when they have the same length and every bit in their pointwise XOR is false.

**Proof.** Induct on the first string, allowing the second string to vary. If the first string is empty, splitting on the second shows that both sides of the equivalence hold exactly when it too is empty. If the first string is nonempty and the second is empty, the length condition fails, as does equality. In the remaining case write the strings as $a::u$ and $b::v$. Equality of these lists is equivalent to $a=b$ and $u=v$; their lengths agree exactly when the tails’ lengths agree. Their pointwise XOR consists of $a\mathbin{\mathrm{xor}}b$ followed by the pointwise XOR of the tails. The induction hypothesis handles the tails, and checking the two possible values of each leading bit shows that $a=b$ exactly when $a\mathbin{\mathrm{xor}}b$ is false. Together these facts give the equivalence.
