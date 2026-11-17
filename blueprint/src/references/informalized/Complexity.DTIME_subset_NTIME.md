<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NTIME.lean :: Complexity.DTIME_subset_NTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Time Is Nondeterministic Time

**Claim.** For every time bound $T$, every language decidable in deterministic time bounded by a constant multiple of $T$ is decidable in nondeterministic time bounded by a constant multiple of $T$.

**Proof.** Take a deterministic decider $M$ for the language, running within the claimed constant multiple of $T$. Regard $M$ as a nondeterministic machine whose two possible transition choices agree with the deterministic transition. The fact `toFinNDTM_haltsWithin_and_accepts_iff` states that this converted machine halts on every choice sequence within the same time bound and that an accepting choice sequence exists exactly when the input belongs to the language. Thus it meets the definition of nondeterministic time with the original constant and bound.

**Key facts.** `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff`.
