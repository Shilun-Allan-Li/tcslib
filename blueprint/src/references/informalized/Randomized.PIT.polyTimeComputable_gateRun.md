<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_gateRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Gate Evaluation

**Claim.** Initializing the encoded gate-evaluation state, iterating the gate-state update for the prescribed number of rounds, and extracting the second component is a polynomial-time computable function.

**Proof.** First construct the initial state by successively pair-encoding the second and first decoded components of the input, then the second component again, and finally two empty lists. The projections are polynomial-time computable (`polyTimeComputable_pairSndD`, `polyTimeComputable_pairFstD`), the empty lists are constant outputs (`polyTimeComputable_const`), and pair encoding preserves polynomial-time computability (`Complexity.PolyTimeComputable.pairEncode`). Thus `gateInit` is polynomial-time computable. Next, apply the polynomial-time gate-state update (`polyTimeComputable_gStep`) repeatedly via the bounded loop. The loop theorem `polyTimeComputable_forLoop` applies because the update preserves the first decoded component (`pairFstD_gStep`) and increases the encoding length by at most $10$ times that component's length plus a linear term (`length_gStep_le`). The bound theorem `forLoop_bound_of_ctx`, with these two properties, gives a quadratic bound on every intermediate loop state; hence the loop is polynomial-time computable. Composing the loop with initialization and then extracting the second decoded component, which is polynomial-time computable (`Complexity.PolyTimeComputable.comp`, `polyTimeComputable_pairSndD`), proves the claim.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_const`, `Randomized.PIT.polyTimeComputable_gStep`, `Randomized.PIT.pairFstD_gStep`, `Randomized.PIT.length_gStep_le`, `Complexity.BinArith.forLoop_bound_of_ctx`, `Complexity.BinArith.polyTimeComputable_forLoop`, `Complexity.PolyTimeComputable.comp`.
