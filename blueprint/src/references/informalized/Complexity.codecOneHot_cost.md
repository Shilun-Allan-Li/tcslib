<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecOneHot_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Hot Encoding Cost Bound

**Claim.** For every finite type $\alpha$, the cost of its one-hot CNF encoding is at most $|\alpha|+1+3|\alpha|^2$.

**Proof.** List the elements of $\alpha$ once. The one-hot encoding consists of one clause requiring at least one element to be selected, followed by one two-literal clause for each ordered pair of distinct elements, requiring that they are not both selected. Each such pair clause has cost three, since the cost of a clause is its length plus one. For each fixed first element there are at most $|\alpha|$ possible second elements, so the total cost of that family is at most $|\alpha|\cdot(3|\alpha|)=3|\alpha|^2$, using the bound on the cost of a concatenated list of clauses (`codecCnfCost_flatMap_le`). The single at-least-one clause has length $|\alpha|$ and therefore cost $|\alpha|+1$. Adding the two contributions, with cost additive under concatenation (`codecCnfCost_append`), gives the stated bound.

**Key facts.** `Complexity.codecCnfCost_flatMap_le`, `Complexity.codecCnfCost_append`.
