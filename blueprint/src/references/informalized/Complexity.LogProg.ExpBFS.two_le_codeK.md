<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.two_le_codeK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for the Code Bound

**Claim.** For every finite nondeterministic Turing machine $N$ over the Boolean alphabet, its code bound $2W+2$, where $W=H+3k+1$, is at least $2$.

**Proof.** The cardinality $H$ and the number $k$ of work tapes are natural numbers, so $W=H+3k+1\ge 1$. Hence $2W+2\ge 2$, as required.
