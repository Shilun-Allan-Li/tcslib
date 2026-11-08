<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/PowTable.lean :: Light.length_powList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power-list length

**Claim.** For natural numbers $b$ and $L$, the list of integers $b^j$ for $j=0,\ldots,L-1$ has length $L$.

**Proof.** The list is obtained by mapping the function that sends $j$ to the integer represented by $b^j$ over the length-$L$ range $[0,1,\ldots,L-1]$. Mapping preserves list length, giving length $L$.
