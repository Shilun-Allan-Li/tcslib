<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Reachability Extension

**Claim.** If $G$ holds at $a$ and the machine reaches $c$ from the one-step successor of $a$ while maintaining $G$ before reaching $c$, then it reaches $c$ from $a$ with the same property.

**Proof.** First, the one-step reachability result gives a reach from $a$ to its successor, with $G$ holding at the sole earlier configuration $a$ (`Complexity.LogProg.MReach.single`). Concatenate this reach with the given reach from that successor to $c$. Transitivity of reachability guarantees that the concatenated run reaches $c$ and that $G$ holds at each configuration before the endpoint (`Complexity.LogProg.MReach.trans`).

**Key facts.** `Complexity.LogProg.MReach.single`, `Complexity.LogProg.MReach.trans`.
