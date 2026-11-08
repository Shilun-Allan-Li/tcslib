<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.registerScale_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling one register by a loop

**Claim.** Under the stated instruction scheme and value bounds, the loop reaches $done$ with the source set to zero and the destination increased by $factor$ times the source’s initial value, preserving all other registers and the invariant and bound at every earlier configuration.

**Proof.** Induct on the initial source value. If it is zero, the test instruction immediately branches to $done$. Both nested updates in the target configuration leave the values unchanged, and the one-step reach with the invariant follows from `AReach.single`.

For a positive source value, write it as $k+1$. The test branches to $down$, and the decrement instruction reduces the source to $k$ and enters $inc(0)$. Let $downv$ denote the values after this decrement. Apply the increment-chain reach (`arm_increments`) to execute the $factor$ increments: the destination becomes its previous value plus $factor$, while the source remains $k$. The total-value hypothesis ensures the destination remains bounded during these increments; the other values remain bounded as well (`register_update_le`). At the end of the chain the program returns to $test$. The new values satisfy the induction hypothesis, since the source has fallen by one and the destination has risen by $factor$. The induction hypothesis now completes the run. The reach-step and reach-transitivity facts (`AReach.step`, `AReach.trans`) concatenate the test step, decrement step, increment chain, and remaining run. Finally, the updates combine to set the source to zero and increase the destination by $factor(k+1)$; the distinctness of the registers ensures the destination update does not alter the source assignment.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.arm_increments`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.trans`.
