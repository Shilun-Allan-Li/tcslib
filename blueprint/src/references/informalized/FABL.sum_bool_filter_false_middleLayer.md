<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.sum_bool_filter_false_middleLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Sum at False

**Claim.** For every nonnegative extended real number $p$, restricting the Boolean sum of the weight $p$ at true and $1-p$ at false to the false value gives $1-p$.

**Proof.** The condition in the sum keeps only `false`. Evaluating the weight there gives $1-p$, and summing this sole term gives the result.
