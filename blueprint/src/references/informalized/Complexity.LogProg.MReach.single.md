<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability in One Step

**Claim.** If $G$ holds at a configuration $a$, then the machine reaches its one-step successor from $a$ while $G$ holds at every configuration strictly before that endpoint.

**Proof.** Take the run length to be $1$. By the definition of iteration, the run ends at the one-step successor of $a$. The only natural time strictly less than $1$ is time $0$, when the run is still at $a$; thus the required property at every earlier configuration is exactly the hypothesis $G(a)$.
