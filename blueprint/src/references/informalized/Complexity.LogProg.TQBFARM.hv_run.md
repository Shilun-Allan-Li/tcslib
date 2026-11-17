<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.hv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Run of the Halving Routine

**Claim.** From the initial halving phase and a state with all registers bounded by $B$, the machine reaches the bit-test phase with $C=0$ and $T=\lfloor s.T/2^{s.C}\rfloor$, preserving the guard and register bound throughout.

**Proof.** The three phases of the halving routine test whether $C$ is zero, decrement it when positive, and halve $T$ before returning to the first phase. The general bounded halving-loop result (\texttt{halve_run}) shows that these repetitions reach the exit with the counter cleared and the scratch register divided by $2$ once per original unit of $C$, hence equal to $s.T/2^{s.C}$. The initial register bounds provide its coordinatewise bound hypothesis via (\texttt{St.Bd.toV}); instantiating the loop with the routine’s three phases gives the claimed run and endpoint.

**Key facts.** `Complexity.LogProg.TQBFARM.St.Bd.toV`, `Complexity.LogProg.halve_run`.
