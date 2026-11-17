<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.ic_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment-Count Register Run

**Claim.** From the index-zero label for $c$, the codec program reaches its next label for $c$, increasing the associated register by the associated count. The prescribed safety condition and the bound on every register hold throughout the run.

**Proof.** Use the increment-chain theorem (`incChain`) on the sequence of labels indexed from zero through the count for $c$. By the program's label definitions, each label before the last increments the register associated with $c$ and advances to the next indexed label. The initial register bounds and the assumed bound on that register after all the increments are precisely the hypotheses needed by the chain theorem. The theorem gives the claimed endpoint assignment and guarantees the guard and register bounds throughout the run.

**Key facts.** `Complexity.Codec.incChain`.
