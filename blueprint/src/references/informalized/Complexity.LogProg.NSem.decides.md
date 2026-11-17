<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Time Characterisation of Acceptance

**Claim.** If every computation from the initial configuration terminates with the guard holding at each preceding live configuration, and acceptance is equivalent to the existence of a finite accepting computation, then some common finite time bound characterizes acceptance using choice sequences of exactly that length.

**Proof.** 1. Apply the finite uniform halting bound for a terminating nondeterministic computation tree (\texttt{NTerm.nhalts}) to obtain $N$ such that every choice sequence of length $N$ halts and all earlier live configurations satisfy the guard. It remains to identify acceptance with the existence of an accepting choice sequence of length exactly $N$.

2. If a length-$N$ choice sequence ends with answer true, it ends in a halted configuration by the bound. Thus it witnesses acceptance directly, giving the implication from a length-$N$ accepting sequence to $P$ by the hypothesis that acceptance is equivalent to $P$.

3. Conversely, suppose $P$ holds. The same equivalence supplies a finite choice sequence $\sigma$ that halts with answer true. If $\sigma$ is shorter than $N$, append $N-|\sigma|$ arbitrary choice bits, say zeros. Once halted, running further bits leaves the configuration unchanged (\texttt{narun_append_of_halted}), so the extended sequence still has answer true. If $\sigma$ is at least $N$ long, take its first $N$ bits. The uniform bound says that this prefix halts; the remaining suffix cannot alter the halted configuration, again by \texttt{narun_append_of_halted}. Hence the prefix already ends with answer true. In either case there is a length-$N$ accepting sequence.

**Key facts.** `Complexity.LogProg.NTerm.nhalts`, `Complexity.LogProg.narun_append_of_halted`.
