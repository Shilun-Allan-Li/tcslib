<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnf_numVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable bound after relabeling

**Claim.** If every variable in every clause of a CNF is mapped by $w$ to an index less than $N$, then the variable count of the relabeled formula is at most $N$.

**Proof.** The variable count is the maximum, with zero as a floor, of the indices occurring in the relabeled clauses after adding one to each index. Take any such index: it comes from some clause and literal of the original formula. By hypothesis its relabeled index is less than $N$, so adding one gives a number at most $N$. Thus every entry contributing to the maximum is at most $N$, and so is the variable count.
