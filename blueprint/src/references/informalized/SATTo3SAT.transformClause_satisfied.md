<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.transformClause_satisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of the Encoded Clause

**Claim.** If some literal in a clause is true under an assignment, then every 3-clause in its encoding is satisfied by the specified extension of that assignment to original and auxiliary variables.

**Proof.** The empty clause cannot satisfy the hypothesis, so consider the remaining length cases. For a clause of length one, two, or three, its sole output clause repeats or lists the translated original literals. Translation preserves each literal’s truth value, so the true literal from the hypothesis satisfies the output clause. For a clause of length at least four, the output begins with a 3-clause containing the translations of the first two literals and the positive auxiliary literal at position zero. If either of the first two literals is true, this clause is satisfied directly. If both are false, the auxiliary assignment makes that positive literal true: its value records that the first two literals are both false. Every subsequent output clause belongs to the chain on the remaining suffix. The chain satisfaction result applies because the original clause has a true literal, translated literals preserve truth values, and each auxiliary variable at the clause’s index has the stipulated value; it therefore shows that all those chain clauses are satisfied (\texttt{SATTo3SAT.buildChain\_all\_satisfied}).

**Key facts.** `SATTo3SAT.buildChain_all_satisfied`.
