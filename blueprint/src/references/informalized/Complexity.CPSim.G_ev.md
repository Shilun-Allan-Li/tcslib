<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.G_ev -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Admissibility of Bounded Encoded Configurations

**Claim.** Every configuration formed from a label, bounded register values, and bounded auxiliary counters, with no output bit, satisfies the simulation invariant at the specified encoded input and bound.

**Proof.** The encoded input is a valid plain encoding: take its unary prefix length to be $n$ and its payload to be the binary representation of $p$. The binary payload is canonical by `canon_bits`. The validity of this input implies the required precondition for the configuration (`preS_A`). For the register bound, consider any of the $R+3$ registers. The definition of the extended assignment gives either one of the original register values, bounded by $B$ by hypothesis, or one of the three auxiliary values, each bounded by its stated hypothesis. Thus every register is at most $B$, completing both parts of the invariant.

**Key facts.** `Complexity.LogProg.canon_bits`, `Complexity.CPSim.preS_A`.
