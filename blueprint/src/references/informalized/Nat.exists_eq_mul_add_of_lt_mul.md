<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.exists_eq_mul_add_of_lt_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Quotient and Remainder Representation

**Claim.** If $t<mn$, then there are natural numbers $a<m$ and $b<n$ such that $t=an+b$.

**Proof.** Take $a=t/n$ and $b=t\bmod n$. The product-bound quotient estimate gives $a<m$ (`Nat.div_lt_of_lt_mul'`), and the product-bound remainder estimate gives $b<n$ (`Nat.mod_lt_of_lt_mul`). The division algorithm then gives $t=(t/n)n+(t\bmod n)=an+b$.

**Key facts.** `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`.
