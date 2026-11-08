<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.accessCheck_dup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under a Doubled Prefix

**Claim.** For Boolean words $w$ and natural numbers $k$, the access check on the word formed by prefixing $w$ with two copies of the same bit equals the access check on $w$.

**Proof.** The decoder reads an equal pair of leading bits as one bit of the first component and then continues decoding the remainder. Consider the two possible values of the repeated bit and whether decoding $w$ succeeds. If it succeeds, decoding the prefixed word produces the same second component as before, with one additional leading bit in the first component. The access check tests only whether the second component is canonical and equals the binary expansion of $k$, so its result is unchanged. If decoding $w$ fails, the decoder's recursive definition shows that decoding the prefixed word fails as well; both checks then return the same empty result.
