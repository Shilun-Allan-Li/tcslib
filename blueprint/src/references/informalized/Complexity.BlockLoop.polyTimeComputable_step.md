<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Closure Under a Block-Loop Step

**Claim.** If the block-loop transformation is defined by polynomial-time computable update and next-state functions, then that transformation is polynomial-time computable.

**Proof.** The transformation first tests whether the accumulator is empty or, if not, whether the countdown component is empty. Both tests are polynomial-time computable (`polyTimeComputable_headNil`, `polyTimeComputable_countdownNil`), so their disjunction is as well (`polyTimeComputable_or`). The two decoding projections are polynomial-time computable (`polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`); composing them gives the countdown component, and composing the tail operation with that component gives the countdown with its first marker removed (`PolyTimeComputable.comp`, `polyTimeComputable_tail`). Pairing these polynomial-time results with the assumed update and next-state computations makes the nonterminal encoded output polynomial-time computable (`PolyTimeComputable.pairEncode`). The terminal output is the constant completed-block encoding (`polyTimeComputable_const`). A polynomial-time conditional on the combined emptiness test selects between the terminal and nonterminal outputs (`polyTimeComputable_ite`). Unfolding the definition of the block-loop step and considering the two emptiness tests shows that this conditional is exactly the stated transformation.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_tail`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BlockLoop.polyTimeComputable_headNil`, `Complexity.BlockLoop.polyTimeComputable_countdownNil`, `Complexity.polyTimeComputable_or`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`.
