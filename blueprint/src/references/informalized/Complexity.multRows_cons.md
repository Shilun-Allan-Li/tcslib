<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multRows_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Row Decomposition of the Row Sum

**Claim.** The sum of rows for the string formed by placing $t$ before $a$ equals the row for $t,b$ at indices $j,p$, plus the sum of rows for $a,b$ at indices $j,p+1$.

**Proof.** Separate the first position of $t::a$ from the remaining positions in the sum over positions of the first string. The first position contributes the row for $t,b$ with indices $j,p$. Every later position has index one greater than its corresponding position in $a$, so its row is counted in the sum for $a,b$ with indices $j,p+1$. Combining these two parts gives the identity.
