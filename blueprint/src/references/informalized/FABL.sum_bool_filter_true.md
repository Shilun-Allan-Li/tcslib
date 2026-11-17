<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.sum_bool_filter_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Sum at True

**Claim.** For every nonnegative extended real number $p$, restricting the Boolean sum of the weight $p$ at true and $1-p$ at false to the true value gives $p$.

**Proof.** The filter retains only the element `true` from the two-element Boolean set. The summand at that element is $p$, so the restricted sum equals $p$.
