<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.oracle_mem_POracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Self-Membership

**Claim.** For every language $O\subseteq\{0,1\}^*$, the language $O$ belongs to the polynomial-time class relative to oracle $O$.

**Proof.** The identity reduction maps each input to itself, so membership in $O$ is preserved and $O\le_p O$ (the reflexivity of polynomial-time reducibility, `PolyTimeReducible.refl`). The closure property that every language polynomial-time reducible to an oracle $O$ belongs to $P^O$ (`mem_POracle_of_polyTimeReducible`) then gives $O\in P^O$.

**Key facts.** `Complexity.PolyTimeReducible.refl`, `Complexity.mem_POracle_of_polyTimeReducible`.
