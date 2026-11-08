<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clSigned_advance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Counts Advance by Displacement

**Claim.** For each coordinate, advancing the two banks of counters changes their signed difference by exactly the assigned displacement.

**Proof.** Fix a coordinate $i$ and split into the three possibilities for its displacement: positive, zero, or negative. The counter-selection rule increments the first-bank counter at $i$ in the positive case, increments neither counter in the zero case, and increments the second-bank counter in the negative case. Since the signed value is the first-bank count minus the second-bank count, these changes alter it by $1$, $0$, and $-1$, respectively. In each case the new signed value is therefore the old one plus the displacement.
