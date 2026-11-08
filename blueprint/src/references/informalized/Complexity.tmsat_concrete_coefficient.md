<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_concrete_coefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concrete simulation coefficient bound

**Claim.** With $L$ the canonical serialization length, $m$ the decoded machine’s state parameter, $q_0$ its initial state, and $B=3L+5(m+1)+20$, the coefficient $3|\alpha|+T_c(|\alpha|)+L+2|\mathrm{bin}(m)|+2q_0+16+B+14$ is at most $3|\alpha|+14T_c(|\alpha|)+50$.

**Proof.** The serialization-length bound (`Complexity.tmsat_serialization_length`) gives $L\le T_c(|\alpha|)$. The serialization parameter bounds (`Complexity.tmsat_serialization_parameters`) give $|\mathrm{bin}(m)|\le L$, $q_0\le L$, and $m+1\le L$. Substitute these inequalities into $B=3L+5(m+1)+20$ and into the other terms involving serialization parameters. The resulting left side is bounded by $3|\alpha|+14L+50$, which is at most $3|\alpha|+14T_c(|\alpha|)+50$ by the bound on $L$.

**Key facts.** `Complexity.tmsat_serialization_length`, `Complexity.tmsat_serialization_parameters`.
