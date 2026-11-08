<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.timed_universal_quantitative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantitative timed universal simulation

**Claim.** For the universal binary Turing machine supplied by the concrete simulation theorem, the decoded machine’s behavior for a time bound $t$ is reproduced on the prescribed paired input within $(3|\alpha|+14T_c(|\alpha|)+50)(t+1)^2$ steps: a halted computation with output $w$ yields $1w$, and absence of a halted computation by time $t$ yields the one-bit output $0$.

**Proof.** Take the universal machine and the two simulation bounds supplied by the concrete timed universal theorem (`Turing.timed_universal_concrete`). For fixed $\alpha$, that theorem gives the same two conclusions with coefficient $3|\alpha|+T_c(|\alpha|)+L+2|\mathrm{bin}(m)|+2q_0+16+B+14$, where $L$ is the canonical serialization length, $m$ is the decoded machine’s state parameter, $q_0$ its initial state, and $B$ its block bound. The coefficient estimate (`Complexity.tmsat_concrete_coefficient`) shows this is at most $3|\alpha|+14T_c(|\alpha|)+50$. Multiplying by $(t+1)^2$ preserves the inequality. The monotonicity of timed computation (`Turing.FinTM.ComputesInTime.mono`) therefore upgrades each of the concrete simulation bounds to the stated bound, for both the halting-output case and the timeout case.

**Key facts.** `Turing.timed_universal_concrete`, `Complexity.tmsat_concrete_coefficient`, `Turing.FinTM.ComputesInTime.mono`.
