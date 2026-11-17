<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.mem_badLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad-Language Membership

**Claim.** A bit string $p$ belongs to the bad language if and only if every bit string $e$ whose length is at most $d.B(p.length+1)^{d.b}$ satisfies the check on the total first and second projections of $p$ and on $e$.

**Proof.** By definition, the bad language consists exactly of those strings $p$ for which the stated universal condition on $e$ holds. Unfolding that definition gives the right-hand side, so the equivalence is reflexive.
