<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_certificate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability Certificate Characterization

**Claim.** The decoded CNF formula is satisfiable exactly when there is a binary word of length $|x|+1$ whose indexed bits, with false assigned beyond its length, satisfy the formula.

**Proof.** Suppose the decoded formula is satisfied by an assignment $a$. Form a word $u$ of length $|x|+1$ by listing the values $a(0),\ldots,a(|x|)$. Every variable index that can affect the formula is less than its number of variables, and that number is at most $|x|$ by the decoded formula bound ( `numVars_decode_le` ). Hence each relevant index lies within the listed range. At such an index, the assignment read from $u$ agrees with $a$; therefore evaluation is unchanged by agreement below the variable bound ( `eval_congr_of_lt_numVars` ). This gives the required certificate. Conversely, given such a word, use its default-false indexed lookup as the assignment itself. Its asserted evaluation is precisely satisfaction, so the formula is satisfiable.

**Key facts.** `Std.Sat.CNF.numVars_decode_le`, `Complexity.eval_congr_of_lt_numVars`.
