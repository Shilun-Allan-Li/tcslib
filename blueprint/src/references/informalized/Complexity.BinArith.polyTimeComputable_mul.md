<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.polyTimeComputable_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-Time Product

**Claim.** The function sending an encoded pair to the binary expansion of the product of its decoded values is polynomial-time computable.

**Proof.** Initialize the multiplication state by encoding the first decoded component together with a state containing the second decoded component and an empty accumulator. This initialization is polynomial-time computable by the component projections, constant-word construction, and polynomial-time pair encoding. The multiplication update itself is polynomial-time computable (`polyTimeComputable_mulStep`), so the iteration theorem gives a polynomial-time computation after $|z|+1$ updates. The required bound on the lengths of intermediate states follows from the multiplication invariant (`mulInv_init`, `mulInv_step`) and the estimate `length_le_of_mulInv`.

For correctness, use the invariant’s measure, the length of the remaining first component of the encoded second component. Each update preserves the invariant and strictly decreases this measure whenever it is positive; when the measure is zero, the update fixes the state (`mulInv_step`). The initial measure is at most $|z|$, since decoding cannot increase length (`length_pairSndD_le`), so after $|z|+1$ updates the measure is zero (`iterate_measure_eq_zero`). The invariant then identifies the accumulator’s decoded value with the product of the original decoded values. Projecting that accumulator and converting it to binary yields the desired output.

**Key facts.** `Complexity.BinArith.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_mulStep`, `Complexity.BinArith.mulInv_init`, `Complexity.BinArith.mulInv_step`, `Complexity.BinArith.length_le_of_mulInv`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.BinArith.length_pairSndD_le`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.pairFstD_pairEncode`, `Complexity.BinArith.pairSndD_pairEncode`.

**Caveat.** The supplied statement of `MulInv` and the definitions of `mulInit` and the invariant’s product accumulator are omitted. The final identification of the accumulator with the product is therefore described at the level indicated by the proof’s invariant projections, rather than its exact invariant equations.
