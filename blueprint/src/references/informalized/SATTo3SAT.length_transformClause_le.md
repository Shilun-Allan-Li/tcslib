<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.length_transformClause_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Clause Encoding Length Bound

**Claim.** For every finite clause $C$ and clause index, encoding $C$ as a list of 3-clauses produces at most $|C|+2$ clauses.

**Proof.** For clauses of lengths zero through three, the definition lists at most two output clauses, and direct counting gives the bound. For a clause of length at least four, the encoding consists of one initial 3-clause followed by a chain built from the remaining literals after the first two. The chain length is at most the number of its input literals (\texttt{SATTo3SAT.length\_buildChain\_le}); hence the total is at most one plus the length of that suffix, which is no more than $|C|+2$.

**Key facts.** `SATTo3SAT.length_buildChain_le`.
