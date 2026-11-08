<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.dec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Decrement Step

**Claim.** If the instruction at $l$ decrements register $r$ and moves to $l'$, the current configuration satisfies the guard, and the resulting configuration has probabilistic semantics with probability $p$, then the current configuration also has probabilistic semantics with probability $p$.

**Proof.** Apply the deterministic-step principle (Complexity.LogProg.PSem.det) to the instruction at $l$. For a decrement instruction, its one-step deterministic transition sends $(l,v,	ext{none})$ to $(l',v',	ext{none})$, where $v'$ agrees with $v$ except that $v'(r)=v(r)-1$ (truncated subtraction). This is exactly the configuration assumed to have semantics with probability $p$. The guard hypothesis supplies the required guard at the current configuration, so the deterministic-step principle gives the conclusion.

**Key facts.** `Complexity.LogProg.PSem.det`.
