<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicCharacter_residue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Character of a Sign Sum

**Claim.** For a sign vector $x$, the cubic character of the sum of its coordinates modulo $3$ is the product over the coordinates of $-\frac12+\frac{\sqrt3}{2}x_i\,\mathrm{i}$.

**Proof.** The character maps a finite sum in $\mathbb Z/3\mathbb Z$ to the product of its values on the summands (`addChar_map_finset_sum_eq_prod`). Apply this to the sum of the coordinate residues to express the character of the total as the product of the characters of the individual coordinates. Each coordinate is a sign, and its character value is the stated factor (`modThreeCubicCharacter_intCast_sign`). Substituting these values into the product proves the formula.

**Key facts.** `FABL.addChar_map_finset_sum_eq_prod`, `FABL.modThreeCubicCharacter_intCast_sign`.
