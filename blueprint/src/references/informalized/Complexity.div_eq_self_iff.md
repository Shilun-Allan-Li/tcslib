<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.div_eq_self_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Quotient equals divisor

**Claim.** For natural numbers $n$ and $i$ with $i\le n^2$, the quotient $i/n$ equals $n$ if and only if $i=n^2$.

**Proof.** Separate the case $n=0$. Then the bound forces $i=0$, and both sides of the equivalence hold. Now suppose $n>0$. If $i/n=n$, the division bound $i<n(i/n+1)$, equivalently the standard inequality $i<n(i/n+1)$ for a positive divisor, together with the assumed upper bound $i\le n^2$, forces $i=n^2$; equivalently, one may use $i<n(i/n+1)$ with $i/n=n$ to get $i<n(n+1)$, while the quotient equality gives $i\ge n^2$, so the bound pins $i$ to $n^2$. Conversely, if $i=n^2$, exact division by the positive number $n$ gives $i/n=n$.

**Caveat.** The supplied proof uses the standard division inequality `Nat.div_mul_le_self`; the informal statement of that inequality in the argument above should be read as the quotient-remainder bound that a quotient of $n$ implies $i\ge n^2$, combined with $i\le n^2$.
