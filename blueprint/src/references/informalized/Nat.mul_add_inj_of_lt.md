<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.mul_add_inj_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Quotient and Remainder

**Claim.** If two expressions $an+b$ and $a'n+b'$ are equal and both remainders are less than $n$, then their quotients and remainders agree: $a=a'$ and $b=b'$.

**Proof.** Recover the quotient of each expression by division by $n$. Since $b<n$, dividing $an+b$ by $n$ gives $a$ (the quotient formula `Nat.mul_add_div_of_lt`); likewise, since $b'<n$, dividing $a'n+b'$ by $n$ gives $a'$. The assumed equality therefore implies $a=a'$. Recovering the remainders by taking the expressions modulo $n$ gives $b$ and $b'$, respectively, because each is less than $n$. The same assumed equality then yields $b=b'$.

**Key facts.** `Nat.mul_add_div_of_lt`.

**Caveat.** The proof also uses the corresponding remainder formula `Nat.mul_add_mod_of_lt`, which is not listed in the supplied upstream facts.
