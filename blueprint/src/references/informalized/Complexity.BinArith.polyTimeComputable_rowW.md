<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.polyTimeComputable_rowW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Row Transformation

**Claim.** The row transformation built from successive component decoding, modular arithmetic, and the prescribed zip iteration and entry transformation is polynomial-time computable.

**Proof.** First extract the components needed to assemble the row's input data. The first component of the input, its first decoded component, the second component nested inside the first, and the corresponding deeper component are all polynomial-time computable by composition of the component projections (`polyTimeComputable_pairFstD`, `polyTimeComputable_slot2`, and `polyTimeComputable_slot3`). Use these projections to construct the nested encoded data for `zipWithW`: one side contains the extracted matrix parameter and the modulus computed by multiplying the encoded operands and reducing modulo that parameter; the other side contains the two auxiliary strings. Multiplication and modular reduction are polynomial-time computable, and pairing and composition preserve polynomial-time computability. Finally apply the entry transformation to the zip iteration. The entry transformation is polynomial-time computable (`polyTimeComputable_entryW`), so the zip-iteration closure result `polyTimeComputable_zipWithW` applies; composing it with the assembled input yields `rowW` and proves the claim.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_mul`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_entryW`, `Complexity.BinArith.polyTimeComputable_zipWithW`, `Complexity.PolyTimeComputable.comp`.
