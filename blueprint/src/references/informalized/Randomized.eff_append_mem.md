<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.eff_append_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficiency of Appended Input

**Claim.** If the language $V$ is decidable in polynomial time, the verifier accepting exactly when $x$ concatenated with $r$ belongs to $V$ is efficient in the polynomial-time verifier model.

**Proof.** Decode a paired input $z$ into its two component strings and concatenate them. The two projections are polynomial-time computable, and concatenation preserves polynomial-time computability (the fact supplied by `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, and `Complexity.PolyTimeComputable.append`). Taking the preimage of $V$ under this polynomial-time map therefore gives a language in polynomial time (`Complexity.preimage_mem_P`). Its complement is also in polynomial time (`Complexity.compl_mem_P`). On a correctly encoded pair, the projections recover exactly $x$ and $r$ (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`), so membership in this preimage is equivalent to the verifier's Boolean decision being true; nonmembership is equivalent to its decision being false. These two polynomial-time languages certify the verifier's efficiency.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.append`, `Complexity.preimage_mem_P`, `Complexity.compl_mem_P`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.indicator_eq_true_iff`, `Randomized.indicator_eq_false_iff`.
