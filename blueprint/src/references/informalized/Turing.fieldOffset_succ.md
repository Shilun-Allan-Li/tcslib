<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.fieldOffset_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive field offsets

**Claim.** For $j<|fs|$, the offset after field $j$ is the offset before it plus the length of that field and one.

**Proof.** The first $j+1$ fields consist of the first $j$ fields followed by field $j$. In the offset sum, this adds exactly the contribution $|fs_j|+1$ to the previous offset, proving the identity.
