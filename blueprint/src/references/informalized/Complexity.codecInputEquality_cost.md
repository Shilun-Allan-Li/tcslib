<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecInputEquality_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input equality formula cost

**Claim.** The CNF formula expressing equality of the two encoded input rows has cost at most $6n$.

**Proof.** The formula is a concatenation, over the $n$ input coordinates, of a two-clause equality check. Each coordinate's pair of clauses has cost at most $6$. The flat-map cost bound (`Complexity.codecCnfCost_flatMap_le`) therefore bounds the total cost by the number of coordinates times $6$. Since the finite range has length $n$, this is $6n$.

**Key facts.** `Complexity.codecCnfCost_flatMap_le`.
