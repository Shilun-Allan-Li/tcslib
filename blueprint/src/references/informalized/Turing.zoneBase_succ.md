<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneBase_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Zone Bases

**Claim.** For every $i\in\mathbb{N}$, the base of zone $i+1$ is the base of zone $i$ plus the capacity of zone $i$.

**Proof.** Since $2^i>0$, the natural-number subtraction in $2^i-1$ behaves as ordinary subtraction. Using $2^{i+1}=2\cdot 2^i$, the left side becomes $2(2\cdot 2^i-1)$, while the right side is $2(2^i-1)+2\cdot 2^i$. Expanding both expressions gives $4\cdot 2^i-2$, so they are equal.
