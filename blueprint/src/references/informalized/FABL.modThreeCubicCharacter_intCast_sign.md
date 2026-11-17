<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicCharacter_intCast_sign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Character on a Sign Residue

**Claim.** For a sign $s\in\{-1,1\}$, the cubic character evaluated at its residue modulo $3$ equals $-\frac12+\frac{\sqrt3}{2}s\,\mathrm{i}$.

**Proof.** A sign is either $1$ or $-1$, so check these two cases. For $s=1$, the character takes the value of the chosen cubic root at $1$ (`modThreeCubicCharacter_one`). Writing that root as $-\frac12+\frac{\sqrt3}{2}\mathrm{i}$ (`modThreeCubicRoot_eq`) gives the desired expression. For $s=-1$, the character takes the square of the root (`modThreeCubicCharacter_neg_one`); the square is $-\frac12-\frac{\sqrt3}{2}\mathrm{i}$ (`modThreeCubicRoot_sq`). This is the required formula with $s=-1$.

**Key facts.** `FABL.modThreeCubicCharacter_one`, `FABL.modThreeCubicRoot_eq`, `FABL.modThreeCubicCharacter_neg_one`, `FABL.modThreeCubicRoot_sq`, `FABL.signValue_one`, `FABL.signValue_neg_one`.
