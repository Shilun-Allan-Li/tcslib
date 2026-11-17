<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_columns_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted multiplication columns

**Claim.** When $|a|+|b|\le n$, the weighted sum of the first $n$ multiplication columns equals the product of the values of $a$ and $b$.

**Proof.** Proceed by induction on $a$. If $a$ is empty, every column is zero (`multColumn_nil`), so both sides are zero. If $a=t::a'$, then $n$ cannot be zero because $|a|+|b|\le n$. Write the positive bound as $n+1$. The leading-bit recurrence expresses the weighted columns through position $n$ as $t$ times the value of the prefix of $b$ of length $n+1$, plus twice the weighted columns of $a'$ through position $n-1$ (`mult_column_prefix_cons`). Since $|b|\le n+1$, that prefix is all of $b$. The induction hypothesis applies to $a'$ with bound $n$, giving $V(a')V(b)$ for the latter column sum. Finally, the recursive definition $V(t::a')=t+2V(a')$ identifies the resulting expression with $V(t::a')V(b)$.

**Key facts.** `Complexity.multColumn_nil`, `Complexity.mult_column_prefix_cons`.
