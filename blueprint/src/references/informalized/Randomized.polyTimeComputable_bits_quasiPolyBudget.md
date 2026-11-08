<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.polyTimeComputable_bits_quasiPolyBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computing Quasipolynomial Budget Bits

**Claim.** The function mapping a bit string $x$ to the binary expansion of $2^{\lfloor\log_2 |x|\rfloor^2+1}$ is polynomial-time computable.

**Proof.** First construct the binary representation of $|x|$. The count-loop construction produces a pair whose first component is precisely the bits of the input length (by the identity for `countLoop`), and extracting that component is polynomial-time computable. Thus the map $x\mapsto |x|.{\rm bits}$ is polynomial-time computable. A finite-state transducer can also produce the all-true string of the same length, and removing the first bit twice from the length-bit string and then transducing gives the seed word `budgetSeed`.\n\nStarting from that seed, repeatedly remove one leading bit. At each iterate, the transducer `zerosAfterZero` emits the block prescribed by the current word. The general polynomial-time iteration result applies because each iterate has length at most the starting word's length; the identity that iterated dropping yields the corresponding suffix verifies this bound. Concatenating the emitted blocks and appending the fixed delimiter `[false, true]` is polynomial-time computable. The stated identity for `bits_quasiPolyBudget` identifies this concatenation with the desired binary expansion, proving the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_countLoop`, `Complexity.BinArith.countLoop_eq`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_transduce`, `Complexity.polyTimeComputable_tail`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_emitIter`, `Complexity.BinArith.iterate_drop_one`, `Complexity.polyTimeComputable_const`, `Randomized.bits_quasiPolyBudget`.
