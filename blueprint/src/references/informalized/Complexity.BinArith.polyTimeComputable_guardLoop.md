<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.polyTimeComputable_guardLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Guarded Loop Step

**Claim.** For polynomial-time computable $g$, the specified guarded loop update is polynomial-time computable.

**Proof.** The update is a block-loop step whose update part keeps the first decoded component, while its next-state part applies the prescribed guarded transformation. The block-loop theorem reduces polynomial-time computability of the whole step to that of these two parts (`BlockLoop.polyTimeComputable_step`). The update part is just the first decoded component, so is polynomial-time computable by the projection result (`polyTimeComputable_pairFstD`). For the next-state part, compose second-component projections to extract the old inner payload, apply $g$, and pair the result with the relevant decoded first component. The length comparison selecting between this result and the unchanged payload is polynomial-time computable by the length-comparison result (`polyTimeComputable_lenLe`), together with the encoding and composition closure properties (`PolyTimeComputable.pairEncode`, `PolyTimeComputable.comp`). Polynomial-time conditional selection then gives the guarded choice (`polyTimeComputable_ite`), and encoding its output with the retained component completes the next-state part.

**Key facts.** `Complexity.BinArith.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_lenLe`, `Complexity.polyTimeComputable_ite`, `Complexity.BlockLoop.polyTimeComputable_step`.
