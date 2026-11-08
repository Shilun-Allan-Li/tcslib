<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.inputPos_stepWith_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Head Movement Bound

**Claim.** After one step under a choice bit, the input-head position is at most one greater than its previous position.

**Proof.** First consider any position $q$ and any allowed movement. The value formula for the clamped movement rule (`moveInputPos_val`) says that a zero move leaves the position unchanged, a right move gives $\min(q+1,n+1)$, and a left move gives $q-1$. Each is at most $q+1$. If the machine is halted, `stepWith` leaves its configuration unchanged, so the bound holds immediately. Otherwise its step applies a transition action, whose input-head position is exactly the result of applying that action’s movement to the old position; the bound just proved therefore gives the claim.

**Key facts.** `Complexity.LogProg.moveInputPos_val`.
