<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Index.lean :: Nat.succ_div_mod_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient and Remainder Away from a Boundary

**Claim.** If $n>0$ and $i\bmod n+1\ne n$, then incrementing $i$ leaves its quotient upon division by $n$ unchanged and increases its remainder by one.

**Proof.** Because $n>0$, the remainder bound gives $i\bmod n<n$. Hence $i\bmod n+1\le n$. Together with the assumption that this quantity is not equal to $n$, this implies $i\bmod n+1<n$. The quotient-and-remainder result below the boundary (`Nat.succ_div_mod_of_lt`) now gives both claimed equalities.

**Key facts.** `Nat.succ_div_mod_of_lt`.
