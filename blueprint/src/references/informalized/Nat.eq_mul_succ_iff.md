<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.eq_mul_succ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient and Remainder Characterization

**Claim.** If $i<n$, then $t=i(n+1)$ holds exactly when both $t/n=i$ and $t\bmod n=i$.

**Proof.** For the forward direction, expand $i(n+1)$ as $in+i$. Since $i<n$, the quotient and remainder formulas for a multiple of $n$ plus a smaller remainder give quotient $i$ and remainder $i$ (`Nat.mul_add_div_of_lt` supplies the quotient formula; the corresponding remainder formula supplies the remainder). For the reverse direction, the division algorithm gives $t=n(t/n)+(t\bmod n)$. Substituting the two assumed equalities yields $t=ni+i=i(n+1)$.

**Key facts.** `Nat.mul_add_div_of_lt`.
