<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_lenEq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Equality on Pairs

**Claim.** For the total projections $\pi_1$ and $\pi_2$ that decode a pair and return the empty word on failure, the function returning $1$ exactly when $|\pi_1(z)|=|\pi_2(z)|$ is polynomial-time computable.

**Proof.** The length test for $|\pi_2(z)|\le |\pi_1(z)|$ is polynomial-time computable (`polyTimeComputable_lenLe`). Applying the same test after swapping the decoded components gives the reverse inequality $|\pi_1(z)|\le |\pi_2(z)|$; the swap is polynomial-time computable, and composition preserves polynomial-time computability (`polyTimeComputable_pairSwap`, `PolyTimeComputable.comp`). The conjunction of these two tests is polynomial-time computable (`polyTimeComputable_and`). Finally, two natural numbers are equal exactly when each is at most the other, so this conjunction gives the desired one-bit output. The proof's decoder identities for encoded pairs (`pairFstD_pairEncode` and `pairSndD_pairEncode`) and a split into equality and the two strict-inequality cases identify that output with the stated equality test.

**Key facts.** `Complexity.polyTimeComputable_lenLe`, `Complexity.polyTimeComputable_pairSwap`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_and`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
