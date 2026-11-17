<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.mem_innerLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-Language Membership

**Claim.** A bit string $w$ belongs to the inner language exactly when, for every bit string $t$, the encoding of $(w,t)$ does not belong to the bad language.

**Proof.** The inner language is defined as the set of strings $w$ satisfying this universal condition over $t$. Thus membership is equivalent to the condition itself, directly by unfolding the definition.
