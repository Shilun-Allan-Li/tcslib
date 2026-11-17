<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.length_pairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length after pairing

**Claim.** Pairing consecutive entries of a list $cs$, with a final unpaired entry allowed, produces a list of length $(|cs|+1)/2$.

**Proof.** Proceed by cases on the list. The empty list produces no pairs, and a singleton remains a singleton; in each case the stated formula gives the same length. For a list with at least two entries, the first two are replaced by one node and the remaining tail is paired recursively. By induction, the result has length $1+(|cs'|+1)/2$, where $cs'$ is the tail after those first two entries. Since $|cs|=|cs'|+2$, this is exactly $(|cs|+1)/2$ by integer arithmetic.
