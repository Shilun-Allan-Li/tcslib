<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.mem_badLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad-language membership characterization

**Claim.** A string $z$ belongs to the bad language exactly when the bad-specification condition holds for its five prescribed decoded components.

**Proof.** The bad language is defined as the set of strings satisfying the bad-specification predicate on the five projections $\mathrm{gx}(z)$, $\mathrm{gU}(z)$, $\mathrm{gu}(z)$, $\mathrm{gj}(z)$, and $\mathrm{gp}(z)$. Unfolding this set membership gives precisely the stated equivalence.
