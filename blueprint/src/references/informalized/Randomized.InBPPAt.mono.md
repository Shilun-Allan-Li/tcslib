<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.InBPPAt.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of randomized verification

**Claim.** If a language has an efficient randomized verifier whose acceptance and rejection probabilities are each at least $p$, then for any $p'\le p$ the same verifier satisfies both bounds at $p'$.

**Proof.** Unpack the assumed verifier and its random-bit bound. Keep that verifier and bound. For each input, the membership case already gives probability at least $p$, and transitivity of the order with $p'\le p$ gives probability at least $p'$. The same argument applies to the nonmembership case.
