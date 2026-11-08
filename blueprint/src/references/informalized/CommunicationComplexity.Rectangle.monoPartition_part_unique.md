<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean :: CommunicationComplexity.Rectangle.monoPartition_part_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of intersecting parts

**Claim.** If two members of a monochromatic rectangle partition contain the same point, then they are equal.

**Proof.** Suppose instead that $R\ne S$. The partition's disjointness condition then says that $R$ and $S$ are disjoint. But the given point belongs to both, contradicting disjointness. Hence $R=S$.
