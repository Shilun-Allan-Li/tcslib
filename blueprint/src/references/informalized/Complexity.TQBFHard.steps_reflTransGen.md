<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean :: Complexity.TQBFHard.steps_reflTransGen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step chains yield reachability

**Claim.** A $k$-step chain under the relation that allows either equality or an encoded machine step induces reflexive transitive reachability between the length-$L$ prefixes of its endpoints by encoded machine steps.

**Proof.** Induct on the number $k$ of steps. At zero steps the endpoints are equal, so their length-$L$ prefixes are equal and are related by reflexivity. For a successor chain, its definition supplies an intermediate string $z$, a chain of $k$ steps from $A$ to $z$, and a final block-step relation from $z$ to $B$. By induction the prefixes of $A$ and $z$ are related by reflexive transitive reachability. If the final relation is equality, then the prefixes of $z$ and $B$ agree, so the induction result already gives the conclusion. If it is the encoded machine-step alternative, taking length-$L$ prefixes makes that same encoded step the final edge; append it to the reachability already obtained.
