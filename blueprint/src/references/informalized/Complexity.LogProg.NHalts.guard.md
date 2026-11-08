<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.guard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Guard Condition

**Claim.** If every choice word of length $N+1$ from $(l,v,r)$ halts and all earlier nonhalted configurations satisfy $G$, then $G$ holds at $(l,v,r)$.

**Proof.** Choose, for example, the word consisting of $N+1$ false choices. Its length is $N+1$, so the assumed property applies. At time zero, the prefix of length zero is empty, and running it leaves the initial configuration $(l,v,r)$ unchanged; that configuration is nonhalted because its state is $l$. The intermediate-configuration clause therefore gives $G(l,v,r)$.
