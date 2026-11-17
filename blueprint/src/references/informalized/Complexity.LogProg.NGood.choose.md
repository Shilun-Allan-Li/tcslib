<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean :: Complexity.LogProg.NGood.choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goodness After a Nondeterministic Choice

**Claim.** If the current configuration satisfies $\mathrm{box}$ and each possible one-step choice leads to a configuration whose runs of length at most $T$ satisfy $\mathrm{box}$, with runs of exactly $T$ ending halted and satisfying $Q$, then runs from the current configuration of length at most $T+1$ satisfy $\mathrm{box}$, and runs of exactly $T+1$ end halted and satisfy $Q$.

**Proof.** For the assertion about runs of length at most $T+1$, consider a choice word $u$. If it is empty, the run stays at the initial configuration, so $\mathrm{box}$ holds by hypothesis. If $u$ begins with a bit $b$, its first step reaches $C_b$ by the stated step equation; the rest of the run is the run on the remaining word from $C_b$. That remaining word has length at most $T$, so the first part of the goodness hypothesis for choice $b$ gives $\mathrm{box}$. For a word $w$ of length exactly $T+1$, the word cannot be empty. Write it as $b$ followed by $w'$. After the first step the run is at $C_b$, and $w'$ has length exactly $T$. The second part of the goodness hypothesis for choice $b$ therefore says the final configuration is halted and satisfies $Q$. In both cases, the decomposition of a run on a nonempty word into its first step and the run on the remaining word is the run-with-cons identity (`Turing.NDTM.runWith_cons`).

**Key facts.** `Turing.NDTM.runWith_cons`.
