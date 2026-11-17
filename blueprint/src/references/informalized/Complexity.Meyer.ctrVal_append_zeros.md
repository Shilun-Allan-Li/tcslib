<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.ctrVal_append_zeros -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending Zeros Preserves Binary Value

**Claim.** For every finite Boolean word $l$ and every $k\in\mathbb{N}$, appending $k$ false bits leaves the binary value unchanged.

**Proof.** Induct on $l$. If $l$ is empty, induct on $k$: appending one more false bit contributes zero, so the value remains zero. If $l=b::l'$, the value is the bit value of $b$ plus twice the value of the tail. The induction hypothesis preserves the tail's value after zeros are appended; substituting this into the defining formula gives the same value for the whole word.
