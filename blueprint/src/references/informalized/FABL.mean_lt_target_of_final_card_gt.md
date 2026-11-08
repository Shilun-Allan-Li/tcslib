<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_lt_target_of_final_card_gt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Below Target During Bribery

**Claim.** If $t\le n$ and the bribery set after $n$ steps has cardinality greater than $t$, then the mean after fixing the coordinates in the bribery set at step $t$ to $1$ is strictly below the target.

**Proof.** Suppose instead that the mean at step $t$ is at least the target. The stability property of the bribery construction then says the sets at all later steps remain unchanged (FABL.briberySetsTo_stable). Taking the later step to be $n=t+(n-t)$ shows that the step-$n$ set equals the step-$t$ set. But the cardinality of a step-$t$ set is at most $t$ (FABL.card_briberySetsTo_le), contradicting the assumed step-$n$ cardinality greater than $t$. Therefore the mean at step $t$ must be strictly below the target.

**Key facts.** `FABL.briberySetsTo_stable`, `FABL.card_briberySetsTo_le`.
