<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationAcceptance_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Acceptance Formula

**Claim.** For a finite-state Turing machine $M$ with $k$ work tapes, if $C\ge |Q|+6k+5$, then the binary serialization of the acceptance formula has length at most $13C^2(s+n+2)^3$.

**Proof.** The hypothesis implies $C\ge1$. The acceptance-formula bound (`Complexity.configurationAcceptance_bounds`) gives serialization length at most $4(C(s+n+1)+3)+1$. Since $C\ge1$, we have $C(s+n+1)+3\le3C(s+n+2)$, so this is at most $12C(s+n+2)+1$. Also $C(s+n+2)\le C^2(s+n+2)^3$ and $1\le C^2(s+n+2)^3$. Combining these inequalities bounds the length by $13C^2(s+n+2)^3$.

**Key facts.** `Complexity.configurationAcceptance_bounds`.
