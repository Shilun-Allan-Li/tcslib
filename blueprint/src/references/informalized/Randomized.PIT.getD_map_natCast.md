<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.getD_map_natCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Defaulted List Lookup and Casting

**Claim.** Casting each entry of a natural-number list into $\mathbb{Z}/k\mathbb{Z}$ and then taking a defaulted lookup gives the cast of the original list's defaulted lookup.

**Proof.** Rewrite defaulted lookup as optional indexed lookup, and note that optional lookup commutes with mapping. If the original lookup is absent, both sides are zero; if it returns an entry $v$, both sides are the cast of $v$. Thus the two expressions agree, including when the index lies outside the list.
