<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/MayTheorem.lean :: FABL.symmetric_and_monotone_iff_isEqualWeightThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric monotone threshold characterization

**Claim.** A sign-valued Boolean function is symmetric and monotone if and only if it is an equal-weight threshold function.

**Proof.** For the forward implication, apply the characterization that every symmetric monotone Boolean function is an equal-weight threshold ($\texttt{isEqualWeightThreshold_of_symmetric_monotone}$). For the reverse implication, use the fact that every equal-weight threshold function is symmetric and monotone ($\texttt{IsEqualWeightThreshold.symmetric_and_monotone}$). Together these give the equivalence.

**Key facts.** `FABL.isEqualWeightThreshold_of_symmetric_monotone`, `FABL.IsEqualWeightThreshold.symmetric_and_monotone`.
