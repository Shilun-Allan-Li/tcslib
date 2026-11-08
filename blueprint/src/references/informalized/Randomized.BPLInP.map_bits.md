<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.map_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapping Lists Through Binary Expansions

**Claim.** For every function $f:\mathbb{N}\to\mathbb{N}$ and every finite list $l$ of natural numbers, mapping $l$ by $a\mapsto$ the binary expansion of $f(a)$ gives the same list of bit strings as first mapping $l$ by $f$ and then taking each binary expansion.

**Proof.** At each position in the list, both expressions apply the same function to the same entry: they produce the binary expansion of $f(a)$. Thus the two maps agree entry by entry, so the resulting lists are equal.
