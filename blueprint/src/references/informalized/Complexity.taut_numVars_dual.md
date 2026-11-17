<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_numVars_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable count under duality

**Claim.** For every DNF formula $\psi$, the variable count of its De Morgan dual equals the variable count of the list of terms of $\psi$ viewed as a CNF formula.

**Proof.** The dual forms a CNF by taking each DNF term as a clause and negating each literal. Variable count is computed by collecting the variable indices from all clauses, adding one to each, and taking their maximum with zero. The dual's clause and literal maps preserve each literal's variable index; negating its polarity changes no index. Consequently the list of indices used in the dual is exactly the list obtained by flattening the original terms and extracting their variable indices. The two maxima, and hence the variable counts, are equal.
