<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SelfUniversal.lean :: Turing.exists_selfUniversal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Space Self-Simulation

**Claim.** For every effective code system for one-work-tape binary machines, there is a deterministic binary machine that simulates each decoded machine on the paired input with linear space overhead.

**Proof.** Use the $k=1$ case of the general self-universal simulation theorem (`exists_selfUniversalK`) for the effective code system derived from the given one. It supplies a universal machine and, for each code, a positive constant $C$; whenever the decoded machine halts with an output at time $t$, the universal machine produces that output at time $C(t+1)$ and uses at most $C(s+1)$ cells, where $s$ bounds the simulated space. Identify the derived code system's machine with the decoded machine using `EffectiveMachineCode.toK_toFinTM`. The assumed space bound is at most $s$, so monotonicity of multiplication by $C$ gives the claimed bound $C(s+1)$.

**Key facts.** `Turing.exists_selfUniversalK`, `Turing.EffectiveMachineCode.toK_toFinTM`.
