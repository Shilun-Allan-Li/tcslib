<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.drop_append_of_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping an Appended List

**Claim.** For lists of gates $gs$ and $ext$, dropping the first $|gs|$ entries from their concatenation leaves exactly $ext$.

**Proof.** The concatenation consists of the entries of $gs$ followed by those of $ext$. Removing the first $|gs|$ entries therefore removes precisely the first list and leaves the second.
