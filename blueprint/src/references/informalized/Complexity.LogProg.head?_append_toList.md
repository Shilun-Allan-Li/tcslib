<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.head?_append_toList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head of an appended optional bit

**Claim.** The head of $l$ with the elements of $o$ appended is the head of $l$ when $l$ is nonempty, and otherwise is $o$.

**Proof.** Split into the two possibilities for $l$. If $l$ is nonempty, appending the list represented by the optional bit does not change its first element, so both sides are the head of $l$. If $l$ is empty, the left side is the head of the list represented by $o$, which is precisely $o$ (including the case where $o$ is absent); the right side also reduces to $o$.
