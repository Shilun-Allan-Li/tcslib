<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_briberySetsTo_final_ge_target -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Bribery Reaches the Target

**Claim.** Under the stated monotonicity and positive-bias hypotheses, the bribery set produced after $n$ steps has mean at least any target strictly below $1$.

**Proof.** Suppose instead that the mean after $n$ steps were below the target. The cardinality result for the bribery sequence then says that its set has cardinality $n$ (FABL.card_briberySetsTo_eq_of_mean_lt). It is a subset of the $n$ coordinates, so a set of this cardinality must be the entire coordinate set. Bribing the entire set gives mean $1$ when the original function is monotone and has positive bias (FABL.mean_bribeFunction_univ_one_of_positiveBias). This contradicts the supposition that the mean is below a target strictly less than $1$. Hence the final mean is at least the target.

**Key facts.** `FABL.card_briberySetsTo_eq_of_mean_lt`, `FABL.mean_bribeFunction_univ_one_of_positiveBias`.
