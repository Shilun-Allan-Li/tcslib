<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Pair Equality Decision

**Claim.** For all binary words $u$ and $v$, the pair comparator on the encoding that doubles each bit of $u$, appends $01$, and then appends $v$ halts within $3|u|+|v|+4$ steps and outputs the bit indicating whether $u=v$.

**Proof.** Write the encoded input as $y=pre\,\langle u,v\rangle$, where $pre$ is the doubled copy of $u$ followed by the separator $01$. Its length is $|pre|=2|u|+2$. The parser result shows that after $2|u|+2$ steps the comparator is in rewind state, with $u$ on the work tape and the head positioned to rewind (`a3n_eq_parse`). The rewind result then returns the work head to zero and enters comparison state in $|u|+1$ additional steps (`a3n_eq_rewind`). Finally, the comparison result scans $v$, halts, and outputs the equality bit in $|v|+1$ steps (`a3n_eq_compare`).

The initial configuration of the comparator agrees with its specified empty work tape and initial head position, so these three phases concatenate by the run-addition law (`runFrom_add`). The total is $(2|u|+2)+(|u|+1)+(|v|+1)=3|u|+|v|+4$. The characterization of computation by the run's halted state and output converts the resulting configuration statement into the claimed computation (`computesInTime_iff`).

**Key facts.** `Complexity.a3n_eq_parse`, `Complexity.a3n_eq_rewind`, `Complexity.a3n_eq_compare`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.computesInTime_iff`.
