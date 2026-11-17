<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Odometer.lean :: Light.digitsLE_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Digits after increasing the length

**Claim.** The list of the first $n+1$ base-$b$ remainders of $c$ consists of $c\bmod b$ followed by the first $n$ remainders of $\lfloor c/b\rfloor$.

**Proof.** Expand the definition of the digit list as a map over the indices from zero to $n$. Splitting off the last index rewrites this range as the initial range of length $n$ together with its endpoint. Mapping the remainder expression over that decomposition gives the first term $c\bmod b$. For every remaining index $k$, the identity $c/b^{k+1}=(c/b)/b^k$ (with natural-number division) identifies the corresponding remainder with the $k$th remainder of $c/b$. Thus the remaining mapped list is exactly the length-$n$ digit list of the quotient.
