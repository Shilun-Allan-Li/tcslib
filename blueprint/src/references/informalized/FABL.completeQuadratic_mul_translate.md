<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadratic_mul_translate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Translation Identity

**Claim.** For $y,z\in\mathbb F_2^n$, the product of the complete quadratic signs at $y$ and $z+y$ equals the sign character of the quadratic bit at $z$ times the Walsh character at $y$ with frequency given by the coordinate sums of $z$ away from each coordinate.

**Proof.** Express each complete quadratic sign as the binary sign character applied to its quadratic bit (`completeQuadratic_apply`). The quadratic-bit addition identity (`completeQuadraticBit_add`) expands the bit at $z+y$ as the bit at $z$, the bit at $y$, and the polar term. By the polar-form dot-product identity (`completeQuadraticPolar_eq_dotProduct`), that polar term is the dot product of $y$ with the frequency whose $i$th coordinate sums the coordinates of $z$ other than $i$. The Walsh-character evaluation formula (`vectorWalshCharacter_apply`) identifies the sign of this dot product with the desired Walsh character. Since an additive character sends a sum to a product, the two factors involving the quadratic bit at $y$ combine to the sign of twice that bit; in characteristic two this bit doubled is zero. What remains is the sign of the quadratic bit at $z$ multiplied by the stated Walsh character.

**Key facts.** `FABL.completeQuadratic_apply`, `FABL.completeQuadraticBit_add`, `FABL.completeQuadraticPolar_eq_dotProduct`, `FABL.vectorWalshCharacter_apply`.
