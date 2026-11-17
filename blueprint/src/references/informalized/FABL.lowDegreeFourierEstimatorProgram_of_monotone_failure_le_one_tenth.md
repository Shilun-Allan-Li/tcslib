<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.lowDegreeFourierEstimatorProgram_of_monotone_failure_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotone Learning Failure Bound

**Claim.** For a monotone Boolean target, the low-degree Fourier estimator at the degree determined by the majority function’s total influence has probability at most $1/10$ of producing a hypothesis whose relative Hamming error exceeds $\epsilon$.

**Proof.** By the total-influence comparison for monotone functions, the target’s total influence is at most that of majority ($\texttt{totalInfluence\_toReal\_le\_majority\_of\_monotone}$). Apply the general total-influence failure bound with $t$ equal to majority’s total influence. Its prescribed degree is then exactly the degree used in this theorem, and it gives the claimed probability bound.

**Key facts.** `FABL.totalInfluence_toReal_le_majority_of_monotone`, `FABL.lowDegreeFourierEstimatorProgram_of_totalInfluence_failure_le_one_tenth`.
