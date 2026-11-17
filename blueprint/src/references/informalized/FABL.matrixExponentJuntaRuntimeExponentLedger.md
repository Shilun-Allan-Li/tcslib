<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.matrixExponentJuntaRuntimeExponentLedger -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runtime Exponent Ledger

**Claim.** The balanced exponent equals $\frac{\omega}{\omega+1}k$; the solver exponent is nonnegative and at most the cutoff; and the maximum of the solver exponent and cutoff is strictly less than $\frac{\omega}{\omega+1}k+1$.

**Proof.** The proof assembles four established facts. First, `matrixExponentJuntaBalancedExponent_eq_fraction` gives the stated formula for the balanced exponent. Next, `matrixExponentJuntaSolverExponent_nonneg` supplies nonnegativity of the solver exponent, and `matrixExponentJuntaSolverExponent_le_cutoff` bounds it by the cutoff. Finally, `matrixExponentJuntaCombinedExponent_lt_fraction_add_one` gives the strict bound on the maximum. Together these are exactly the four components of the ledger.

**Key facts.** `FABL.matrixExponentJuntaBalancedExponent_eq_fraction`, `FABL.matrixExponentJuntaSolverExponent_nonneg`, `FABL.matrixExponentJuntaSolverExponent_le_cutoff`, `FABL.matrixExponentJuntaCombinedExponent_lt_fraction_add_one`.
