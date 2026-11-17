<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multRow_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Row Decomposition

**Claim.** The row sum for the string formed by placing $u$ before $b$ equals the contribution $tu$ when $k=j$, plus the row sum for $t,b$ with indices $j,k+1$.

**Proof.** Separate the first position of the list $u::b$ from the remaining positions. The first position contributes $tu$ precisely when $k=j$, and contributes $0$ otherwise. Each remaining position is one place farther into the list, so its index condition is the one defining the row sum for $t,b$ with second index $k+1$. Adding these contributions gives the stated decomposition.
