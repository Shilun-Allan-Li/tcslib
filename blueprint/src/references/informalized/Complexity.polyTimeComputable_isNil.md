<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_isNil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Emptiness Test

**Claim.** The function returning the one-bit word $1$ exactly on the empty input, and $0$ otherwise, is polynomial-time computable.

**Proof.** Encode the pair consisting of the empty word and the input $w$. This encoding is polynomial-time computable by pairing the constant empty-word function with the identity function (`PolyTimeComputable.pairEncode`, `polyTimeComputable_const`, and `polyTimeComputable_id`). Apply the polynomial-time test that returns $1$ exactly when the second decoded component has length at most the first decoded component's length (`polyTimeComputable_lenLe`), using closure under composition (`PolyTimeComputable.comp`). For an encoded pair $([],w)$, the decoder recovers those two components (`pairFstD_pairEncode` and `pairSndD_pairEncode`), so the test asks whether $|w|\le 0$. This holds exactly when $w$ is empty, as required.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_lenLe`, `Complexity.PolyTimeComputable.comp`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
