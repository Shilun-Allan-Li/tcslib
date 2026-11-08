<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.width_blockMinterm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a Block Minterm

**Claim.** For $m\ge 7$, a block index $b$, and a sign assignment to the $2m$ block coordinates, the corresponding block minterm has width exactly $2m$.

**Proof.** The block minterm's list of literals is obtained by mapping the full finite set of block coordinates into the literal list. Mapping preserves the list length, so its width is the cardinality of that full coordinate set, namely $m+m=2m$.
