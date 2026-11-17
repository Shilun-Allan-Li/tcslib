<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.succ_div_mod_of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient and Remainder at a Boundary

**Claim.** If $i\bmod n+1=n$, then incrementing $i$ increases its quotient upon division by $n$ by one and resets its remainder to zero.

**Proof.** The hypothesis forces $n>0$. Write $i=(i/n)n+i\bmod n$, using the quotient–remainder identity. Since $i\bmod n+1=n$, adding one to $i$ changes the remainder contribution into exactly one more copy of $n$. Thus $i+1=(i/n+1)n+0$. The quotient formula `Nat.mul_add_div_of_lt` applied with remainder zero (which is less than $n$) gives $(i+1)/n=i/n+1$. The corresponding remainder formula gives $(i+1)\bmod n=0$.

**Key facts.** `Nat.mul_add_div_of_lt`.

**Caveat.** The proof also uses `Nat.div_add_mod'` and `Nat.mul_add_mod_of_lt`, neither of which is listed in the supplied upstream facts.
