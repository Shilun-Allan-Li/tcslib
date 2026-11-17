<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.SameOn.cell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement at a specified cell

**Claim.** If two memories agree at every index satisfying the predicate that an index equals $b$, then their values at $b$ agree.

**Proof.** Apply the assumed agreement at the index $b$ itself: the predicate holds there by reflexivity of equality, so $\mu'(b)=\mu(b)$.
