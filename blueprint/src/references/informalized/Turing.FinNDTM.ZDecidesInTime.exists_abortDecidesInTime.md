<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Turing.FinNDTM.ZDecidesInTime.exists_abortDecidesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time aborting decision procedure

**Claim.** Under the given polynomial total-nonhalting bound and correct-output condition, there are natural-number constants $K,E$ and a finite nondeterministic machine $N'$ that halts within $K(|x|^E+1)$ steps on every branch, never outputs the incorrect indicator at that length, and outputs the correct indicator with probability at least $1/2$.

**Proof.** Choose a deterministic clock machine that, on inputs of length $n$, produces a unary word of length $m(n)=(4c+1)(n+1)^{e+1}$, with running time bounded by $c_S(n+1)^{e+2}$ for some constant $c_S$. This length is at least $n$ and at least twice the original bound $c(n^e+1)$. The clock-host construction combines this clock with $N$: its bounded-time branches simulate the original machine for the chosen horizon, and any output that certifies a halt is correct by the assumed correctness of $N$. For the probability guarantee, apply the truncation estimate at horizon $m(|x|)$. Since $m(|x|)
ot<2c(|x|^e+1)$, the lower bound $1-c(|x|^e+1)/m(|x|)$ is at least $1/2$. Identifying the clocked machine's successful attempts with halting runs of $N$ gives the stated success probability. Finally, the clock-host runs in at most $c_S(n+1)^{e+2}+2m(n)+3$ steps. The polynomial upper-bound lemma `add_mul_succ_pow_le` absorbs this expression into $K(n^{e+2}+1)$ with $K=(c_S+2(4c+1)+3)2^{e+2}$ and $E=e+2$. Increasing the time bound preserves all three requirements, so the constructed machine satisfies the claimed bound.

**Key facts.** `Turing.FinTM.computesFunInTime_polyUnary`, `Turing.FinNDTM.ExpTimeLe.one_le`, `Turing.FinNDTM.ZDecidesInTime.truncate`, `Randomized.attemptBit_eq_some`, `Turing.FinNDTM.haltRun_eq_some_iff`, `Randomized.clockHost_abortDecides`, `Randomized.randProb_congr`, `Turing.FinNDTM.AbortDecidesInTime.mono`, `Randomized.add_mul_succ_pow_le`.
