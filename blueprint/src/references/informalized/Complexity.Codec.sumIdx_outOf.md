<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.sumIdx_outOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding summary indices

**Claim.** For each index $o\in\{0,1,2\}$, the prescribed output list has summary index $o$.

**Proof.** There are three possibilities. Index $0$ decodes to the empty list, whose summary is empty and hence has index $0$. Index $1$ decodes to $[1]$, whose summary is accepting and has index $1$. Index $2$ decodes to $[0]$, which is neither empty nor exactly $[1]$, so its summary is dead and has index $2$.
