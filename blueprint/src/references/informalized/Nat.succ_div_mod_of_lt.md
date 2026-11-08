<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.succ_div_mod_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient and Remainder Below a Boundary

**Claim.** If $i\bmod n+1<n$, then incrementing $i$ leaves its quotient upon division by $n$ unchanged and increases its remainder by one.

**Proof.** Write $i=(i/n)n+i\bmod n$ by the quotient–remainder identity. Adding one gives $i+1=(i/n)n+(i\bmod n+1)$. The assumed strict bound makes this new remainder less than $n$. Therefore the quotient formula `Nat.mul_add_div_of_lt` identifies $(i+1)/n$ with $i/n$, and the corresponding remainder formula identifies $(i+1)\bmod n$ with $i\bmod n+1$.

**Key facts.** `Nat.mul_add_div_of_lt`.

**Caveat.** The proof also uses `Nat.div_add_mod'` and `Nat.mul_add_mod_of_lt`, neither of which is listed in the supplied upstream facts.
