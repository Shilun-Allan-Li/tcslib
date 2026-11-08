<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.vectorOfList_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from Indexed Entries

**Claim.** If a list has length $m$, then forming the function on indices $0,\ldots,m-1$ by reading its entries and applying the list constructor indexed by that function recovers the original list.

**Proof.** The proof establishes equality of the two lists by comparing their lengths and then their entries at every valid index. The reconstructed list has length $m$, matching the original list because its length is assumed to be $m$. At each index below this length, the indexed list constructor returns the value of the function there; by definition that function reads the corresponding entry of the original list. The entries therefore agree at every valid index, and lists with equal lengths and equal entries at all valid indices are equal.
