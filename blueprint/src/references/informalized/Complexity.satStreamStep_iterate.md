<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamStep_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the Encoded State Update

**Claim.** For every input bit string $x$, streaming state $s$, and $k\ge 0$, iterating the encoded next-state function $k$ times from the encoding of $s$ gives the encoding of the state obtained by iterating the structured round-state update $k$ times from $s$.

**Proof.** Induct on $k$. At zero iterations, both sides are the encoding of $s$. For the successor step, use the induction hypothesis to replace the first $k$ encoded updates by the encoding of the structured state after $k$ updates. One further encoded update reads that encoding back as the same structured state, by the fact that reading an encoded state recovers it ($\mathrm{satStreamRead\_word}$); it then encodes the state after one more round. This is the right-hand side after $k+1$ structured updates.

**Key facts.** `Complexity.satStreamRead_word`.
