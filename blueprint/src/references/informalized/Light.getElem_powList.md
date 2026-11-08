<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/PowTable.lean :: Light.getElem_powList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of the power list

**Claim.** For $j$ within the list of powers of $b$ of length $L$, its entry at index $j$ is $b^j$, viewed as an integer.

**Proof.** The power list is formed by mapping the function $k\mapsto b^k$ over the list of natural numbers from $0$ through $L-1$. At an in-range index $j$, the indexed entry of this mapped range is the image of the entry $j$ of the range, which is $j$. Therefore the entry is $b^j$, cast to the integers.
