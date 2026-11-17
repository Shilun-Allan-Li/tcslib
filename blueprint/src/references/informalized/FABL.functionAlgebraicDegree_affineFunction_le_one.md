<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Affine.lean :: FABL.functionAlgebraicDegree_affineFunction_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of an affine Boolean function

**Claim.** The algebraic degree of the affine Boolean function $x\mapsto b+a\cdot x$ is at most $1$.

**Proof.** The ANF coefficients of this affine function are given by its explicit affine coefficient formula (`FABL.anfCoeff_affineFunction`). By the characterization of degree at most $1$, it suffices to show that every subset with a nonzero coefficient has size at most one (`FABL.algebraicDegree_le_iff`). Suppose instead that such a subset has size greater than one. It is then nonempty and is not a singleton. The affine coefficient formula gives coefficient zero for any subset that is neither empty nor a singleton, contradicting the assumed nonzero coefficient. Hence every supported subset has size at most one.

**Key facts.** `FABL.anfCoeff_affineFunction`, `FABL.algebraicDegree_le_iff`.
