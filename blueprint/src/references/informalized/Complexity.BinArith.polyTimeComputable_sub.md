<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.polyTimeComputable_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Subtraction

**Claim.** The function that takes a bit string, extracts its two components using the total projections, interprets them as natural numbers with least significant bit first, subtracts the second from the first by truncated subtraction, and returns the result’s binary expansion is polynomial-time computable.

**Proof.** Let $a$ and $b$ be the natural numbers represented by the first and second projected components. The comparison $a<b$ is polynomial-time computable, as is a constant function returning the empty word. In parallel, a finite-state serial subtraction procedure processes the projected bit strings (padded to a common length); its output is polynomial-time computable, and normalizing that output by converting it to the canonical binary expansion is polynomial-time computable by closure under composition. The serial-subtraction specification says that its final borrow bit records whether $b>a$, and, when $b\le a$, its output represents $a-b$ (`Complexity.BinArith.serial_sub_spec`). Now split on the comparison. If $a<b$, truncated subtraction gives zero, whose binary expansion agrees with the empty-word default. If $a\ge b$, the serial output represents $a-b$, so normalization produces precisely its binary expansion. Polynomial-time conditional selection combines these branches using the polynomial-time comparison (`Complexity.polyTimeComputable_ite`), proving the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.polyTimeComputable_serial`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_normBits`, `Complexity.polyTimeComputable_ite`, `Complexity.BinArith.serial_sub_spec`.
