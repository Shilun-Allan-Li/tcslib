<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean :: Complexity.LogProg.NGood.imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Implication for the Terminal Property

**Claim.** If every run of length at most $T$ satisfies $\mathrm{box}$, every run of length exactly $T$ halts and satisfies $Q$, and $Q$ implies $Q'$, then the same runs satisfy the terminal condition with $Q'$ while retaining the box property.

**Proof.** The definition has two parts. Keep its first part unchanged: the assumed box property already applies to every choice word of length at most $T$. For any choice word of length exactly $T$, the second assumption gives both halting and $Q$ at its final configuration; applying the implication from $Q$ to $Q'$ gives the required terminal property.
