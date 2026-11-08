<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.totalWeight_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total weight after erasing an edge

**Claim.** For an edge $e$ occurring in $\mathit{edges}$, the total weight of the list equals $e$'s weight plus the total weight after deleting its first occurrence.

**Proof.** Because $e$ occurs in the list, the list can be rearranged as $e$ followed by the list obtained by erasing that occurrence. Applying the weight function preserves this rearrangement, and a sum is unchanged by rearranging its terms. The sum of the rearranged list is the weight of $e$ plus the sum of the remaining weights, giving the stated identity.
