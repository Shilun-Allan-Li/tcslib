<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.card_le_functionAlgebraicDegree_of_anfCoeff_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Supported Coefficient

**Claim.** If the coefficient of a set $S$ in the algebraic normal form of $f$ is nonzero, then $|S|$ is at most the algebraic degree of $f$.

**Proof.** By definition, the algebraic degree is the supremum of the cardinalities of sets in the support of the coefficient function. The nonzero coefficient hypothesis says precisely that $S$ belongs to this support, by the support-membership characterization (`FABL.mem_anfSupport`). Its cardinality is therefore bounded by that supremum.

**Key facts.** `FABL.mem_anfSupport`.
