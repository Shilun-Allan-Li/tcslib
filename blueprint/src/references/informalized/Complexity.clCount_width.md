<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Width Bound

**Claim.** If $n<2^w$, then the binary representation of $n$ has at most $w$ bits.

**Proof.** Proceed by the binary recursion for $n$, generalizing over $w$. For $n=0$, its bit list is empty, so the bound holds. Otherwise write $n$ as the binary constructor determined by a bit $b$ and a smaller number. If $w=0$, the hypothesis forces $n=0$, contradicting this nonzero binary-constructor case. If $w=w'+1$, the binary representation is the bit $b$ appended to the representation of the smaller number, so its length is one more. The inequality $n<2^{w'+1}$ implies that the smaller number is less than $2^{w'}$; applying the induction hypothesis bounds its bit length by $w'$. Adding one gives the desired bound by $w'+1$.
