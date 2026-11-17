<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThree_eq_cubicRootFilter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic root filter

**Claim.** The indicator of coordinate sums divisible by $3$ equals $\frac13+\frac23\operatorname{Re}\left(\prod_{i=1}^n\left(-\frac12+\frac{\sqrt3}{2}x_i\,\mathrm{i}\right)\right)$.

**Proof.** The proof combines three facts. First, the mod-three indicator equals $1$ when the residue of the coordinate sum is zero and $0$ otherwise (\texttt{modThree_eq_residueIndicator}). Second, the cubic root filter says that for any residue $a$ modulo $3$, this zero-residue indicator is $\frac13+\frac23$ times the real part of its cubic character (\texttt{modThreeCubicFilter}). Finally, the character of the sum of the coordinate residues factors as the product of the individual coordinate characters, each given by the corresponding cubic factor (\texttt{modThreeCubicCharacter_residue}). Substituting the factorization into the root-filter expression gives the claimed product formula.

**Key facts.** `FABL.modThree_eq_residueIndicator`, `FABL.modThreeCubicFilter`, `FABL.modThreeCubicCharacter_residue`.
