<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.pmfExpectation_le_bestLocalLabel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Best Local Label Dominates the Average

**Claim.** The expected affected-constraint count at a variable is at most the count obtained by fixing that variable to its selected best local label.

**Proof.** For every label, its conditional affected-constraint count is at most the count at a maximizing label, by the defining property of a finite maximizer (`le_finiteMaximizer`). Averaging these pointwise inequalities under the variable’s probability law preserves the inequality (`pmfExpectation_mono`). The average of a constant function is that same constant (`pmfExpectation_const`), so the averaged upper bound is precisely the count for the best local label.

**Key facts.** `FABL.le_finiteMaximizer`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
