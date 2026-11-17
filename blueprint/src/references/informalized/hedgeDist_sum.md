<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: hedgeDist_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hedge Distribution Normalization

**Claim.** At every round, the Hedge distribution sums to one over all experts.

**Proof.** The Hedge distribution is the Hedge weight divided by the potential, which is the sum of those weights. Taking the common denominator out of the finite sum gives the sum of all weights divided by the potential. The potential is strictly positive, so this quotient is $1$.

**Key facts.** `potential_pos`.
