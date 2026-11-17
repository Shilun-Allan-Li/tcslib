<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.polyTimeComputable_powStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Exponentiation Step

**Claim.** The specified update on nested encodings, including its stopping conditions and modular products, is polynomial-time computable.

**Proof.** The update first tests whether the exponent counter is empty or the base has value zero. Both tests are polynomial-time computable, as is their disjunction; the branch that returns the input is the identity. In the other branch, form the next nested encoding from the preserved base, the counter with its first bit removed, and two modular products. Each product-then-remainder operation is polynomial-time computable: extract the needed components, pair them, apply polynomial-time multiplication, pair the product with the base, and apply polynomial-time modular reduction. The final accumulator is chosen by testing the first counter bit: if it is one, replace it by its modular product with the current factor; otherwise retain it. The needed nested components are available by the polynomial-time slot projections, while reading the first bit and dropping it are polynomial-time operations. Pairing these computed components and composing the conditional branches yields a polynomial-time implementation of the whole update.

**Key facts.** `Complexity.polyTimeComputable_slot2`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_slot4`, `Complexity.BinArith.polyTimeComputable_mul`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_headD`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_or`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_tail`.
