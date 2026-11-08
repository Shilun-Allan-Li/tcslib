<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_selT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Selector Test

**Claim.** For every choice of the parameters, the function sending a bit string to the one-bit string containing the selector value is polynomial-time computable.

**Proof.** First compute the nested second-pair projection of the first-pair projection of the input; composition of polynomial-time functions gives this computation (`PolyTimeComputable.comp`, `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`). For each fixed offset $k$, the block length is the length of that nested projection. A unary string of this length is polynomial-time computable by composing the unary-length construction with the projections. A unary string of length $k$ times that block length is also polynomial-time computable by `pt_rep_mul`. Using these strings as length controls, `pt_drop` followed by `pt_take` computes the length-sized block beginning at offset $k$ in the second projection of the input. Thus each required block is polynomial-time computable. The equality test for each pair of blocks is polynomial-time computable by `pt_eq`. Combine the first two equalities with conjunction, do the same for the other two, and combine the resulting tests with disjunction. The polynomial-time conjunction and disjunction constructions give exactly the one-bit selector output.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_unary`, `Complexity.TQBFHard.pt_rep_mul`, `Complexity.TQBFHard.pt_drop`, `Complexity.TQBFHard.pt_take`, `Complexity.TQBFHard.pt_eq`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_or`.
