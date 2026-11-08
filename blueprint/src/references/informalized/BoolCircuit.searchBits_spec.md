<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchBits_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of sequential bit search

**Claim.** If a length-$m$ list is related to $y$, then the sequential search produces a length-$m$ list related to $y$.

**Proof.** Induct on the prefix length $j\le m$, proving that the prefix produced after $j$ stages has an extension to a related list of length $m$. At $j=0$, the assumed witness itself supplies that extension. For the step from $j$ to $j+1$, take an extension of the current prefix and test the prefix obtained by appending true. The circuit specification says that this test succeeds exactly when that candidate prefix has a related completion. If it succeeds, the new prefix therefore has such a completion. If it fails, write the old completion as the current prefix followed by a first remaining bit and a tail; its first remaining bit cannot be true, since that would give a completion of the tested prefix. It is thus false, and the old completion witnesses that appending false has a related completion. Finally apply the induction result at $j=m$. The produced prefix has length $m$ (by `length_searchBits`), so its remaining completion must be empty; the extension property then gives the desired relation.

**Key facts.** `BoolCircuit.length_searchBits`.
