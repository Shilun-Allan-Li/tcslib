<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.getElem?_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup after dropping a prefix

**Claim.** If dropping the first $p-1$ entries of $y$ gives $rest$, then the optional entry of $y$ at index $p-1+i$ is the optional entry of $rest$ at index $i$.

**Proof.** Replace $rest$ by the equal list $y.drop (p-1)$. The list lookup identity for a list after dropping a prefix, `List.getElem?_drop`, says that looking up index $i$ in this suffix is the same as looking up index $(p-1)+i$ in the original list. This is the desired equality.
