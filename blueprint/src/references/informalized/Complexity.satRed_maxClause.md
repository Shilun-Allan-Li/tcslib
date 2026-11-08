<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_maxClause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum scan of a clause

**Claim.** For a serialized clause between a prefix and suffix, the machine reaches state $2$ just after the clause in at most twice its serialized length, with counter length equal to the maximum of its initial length and the clause's largest variable index plus one (or zero for the empty clause). The counter head stays at zero, and the second tape, its head, and the output are unchanged.

**Proof.** Induct on the clause. For the empty clause, its serialization is the single false delimiter. One transition reads that delimiter, advances the input head, and changes state $3$ to state $2$, without changing either work tape or the output. This takes one step, within the stated bound, and the counter length remains $n$.

For a clause consisting of a literal $(v,\mathrm{pol})$ followed by a tail clause, split its serialization into the literal encoding and the tail encoding. First apply the maximum-scan result for one literal (\texttt{Complexity.satRed\_maxLiteral}) to the head literal. It takes $2v+5$ steps, leaves the machine in state $3$ just after that literal, and changes the counter length to $\max(n,v+1)$ while returning the counter head to zero. Apply the induction hypothesis to the tail, starting from that configuration. It reaches state $2$ just after the entire clause, with counter length $\max(\max(n,v+1),\mathrm{satClauseVars}(C))$, which is the maximum for the whole clause. The runs concatenate by the run-addition law (\texttt{Turing.MultiTapeTM.runFrom\_add}); the serialization length is the literal length plus the tail length, so the two bounds sum to twice the whole serialization length. The unchanged tape, head, and output data are preserved by both stages.

**Key facts.** `Complexity.satRed_maxLiteral`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.satRed_move`, `Turing.moveInputPos_pos_of_ne_right`.
