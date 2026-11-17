<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.mul_add_div_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient of a Multiple Plus a Small Remainder

**Claim.** For natural numbers $a,b,n$ with $b<n$, the quotient $(an+b)/n$ is $a$.

**Proof.** Since $b<n$, the divisor $n$ is positive. Commuting the factors in $an$ puts the numerator in the form $na+b$. The quotient of a multiple of a positive divisor plus a remainder smaller than that divisor is the multiplier, and the remainder contributes zero to the quotient. Hence $(an+b)/n=a$.
