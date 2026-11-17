<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.polyTimeComputable_divLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Division Loop

**Claim.** The function obtained by applying the division step $|z|+1$ times to the prescribed division initialization of $z$ is polynomial-time computable.

**Proof.** The initialization `divInit` is polynomial-time computable: it pairs the decoded second component with the reverse of the decoded first component and two empty fields. The division step is polynomial-time computable by the upstream step result. To bound all intermediate states, the invariant `DivInv z` holds at initialization (`divInv_init`) and is preserved by each division step (`divInv_step`). Induction over the iteration count through `iterate_invariant` therefore gives `DivInv z` for every intermediate state. The invariant's length estimate `length_le_of_divInv` bounds each such state by $7(|z|+1)$. Finally, `polyTimeComputable_iterate` applies to this polynomial-time initialization and step, with $|z|+1$ iterations and the established linear intermediate-state bound.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_divStep`, `Complexity.BinArith.divInv_init`, `Complexity.BinArith.divInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.length_le_of_divInv`, `Complexity.BinArith.polyTimeComputable_iterate`.
