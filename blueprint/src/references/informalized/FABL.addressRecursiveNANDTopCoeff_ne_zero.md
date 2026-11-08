<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.addressRecursiveNANDTopCoeff_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero NAND Top Coefficient

**Claim.** For every depth $d\in\mathbb{N}$, the top correlation of the depth-$d$ recursively composed two-input NAND function is nonzero.

**Proof.** Induct on the depth. At depth zero, the coefficient is $1$, so it is nonzero. At the next depth, the recurrence says the coefficient is the square of the preceding coefficient divided by $2$. The square of a nonzero real number is nonzero, and division by the nonzero number $2$ preserves nonvanishing. The claim follows at every depth.

**Key facts.** `FABL.addressRecursiveNANDTopCoeff_succ`.
