<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: potential_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the potential

**Claim.** With at least one expert, the Hedge potential at every time is strictly positive.

**Proof.** Each expert's weight is a real exponential and hence is strictly positive (\texttt{hedgeWeight\_pos}). The potential is the finite sum of these positive weights. Since the index set of experts is nonempty, a finite sum of strictly positive terms is strictly positive.

**Key facts.** `hedgeWeight_pos`.
