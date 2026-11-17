<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_guess_word_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Captured Word

**Claim.** If two guessing-phase configurations built from the same scheduler configuration and words $u$ and $v$ are equal, then $u=v$.

**Proof.** Equality of configurations implies equality of their tape contents at every tape and every integer cell. In particular, compare the auxiliary buffer tape at the cell indexed by $i$. In a guessing-phase configuration this cell contains the $i$th entry of the stored word whenever that entry exists. Hence the two words have the same entries at every index, including the same extent of defined entries. Extensionality of lists from their indexed entries then gives $u=v$.
