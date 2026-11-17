<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.POracle_eq_P_of_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Oracle Collapse

**Claim.** If the oracle language $O$ is decidable in polynomial time, then polynomial-time computation with oracle access to $O$ gives exactly the ordinary polynomial-time class: $\mathrm{P}^O=\mathrm{P}$.

**Proof.** The inclusion $\mathrm{P}\subseteq\mathrm{P}^O$ is the general fact that an ordinary polynomial-time computation can be carried out with oracle access (\texttt{Complexity.P_subset_POracle}). For the reverse inclusion, take a language $L\in\mathrm{P}^O$. It has a deterministic oracle decider with a bound of the form $c(n^k+1)$, while the hypothesis that $O\in\mathrm{P}$ supplies an ordinary decider for $O$ with running time bounded by $C(n+1)^d$ (\texttt{Complexity.mem_P_iff}). Replace each oracle query by a computation of this decider. Since a computation taking $T(n)$ steps can submit queries of length at most the input and computation size accounted for by the simulation, the resulting ordinary machine decides $L$ within a polynomial bound. Precisely, the oracle-elimination result gives a plain decider with bound $a(T(n)+1)(T(n)+1+\tau(T(n)))$, where $\tau(m)=C(m+1)^d$ is monotone (\texttt{Turing.FinOracleTM.exists_plain_decider}). Substituting $T(n)=c(n^k+1)$ gives the displayed polynomial time bound used in the proof. The arithmetic estimate \texttt{Complexity.b1_budget} bounds it by a constant times $n^{k(d+2)}+1$, so the resulting language belongs to $\mathrm{P}$ by the polynomial-time bound criterion (\texttt{Complexity.mem_P_of_dtime_le}). Together the two inclusions give equality.

**Key facts.** `Complexity.P_subset_POracle`, `Complexity.mem_P_iff`, `Turing.FinOracleTM.exists_plain_decider`, `Complexity.b1_budget`, `Complexity.mem_P_of_dtime_le`.
