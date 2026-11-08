<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.briberySetsTo_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Bribery Procedure

**Claim.** For positive $n$, the set at stage $t+1$ is formed by adding a maximum-influence coordinate of the function bribed on the stage-$t$ set when its mean is below the target, and is otherwise left unchanged.

**Proof.** Unfolding the recursive definition at stage $t+1$ gives exactly the stated conditional: the recursive call first produces the stage-$t$ set, then the mean test determines whether the maximizing coordinate is inserted or the set is retained.
