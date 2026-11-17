<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.sum_bool_filter_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Sum at False

**Claim.** For every nonnegative extended real number $p$, restricting the Boolean sum of the weight $p$ at true and $1-p$ at false to the false value gives $1-p$.

**Proof.** The filter retains only the element `false` from the two-element Boolean set. At that element the summand is $1-p$, so the restricted sum has this single value and equals $1-p$.
