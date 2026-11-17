<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/CoNP.lean :: Complexity.compl_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure of Polynomial Time

**Claim.** Every binary language decidable in polynomial time by a finite deterministic Turing machine has a complement that is also decidable in polynomial time.

**Proof.** Represent the given polynomial-time decider by constants $C,d$ and a machine whose running time is bounded by $C(n+1)^d$ (mem_P_iff). Its output is the characteristic bit of membership. A timed deterministic postprocessor can flip this bit: the machine computing the Boolean map that sends true to false and false to true runs in linear time (computesFunInTime_ifEq). Composing the original decider with this postprocessor yields a machine deciding the complement, with time bounded by a constant times the original time plus the postprocessing time (computesFunInTime_comp).

The resulting bound is a constant multiple of $C(n+1)^d+a(C(n+1)^d+1)+1$ for some fixed $a$. Since $(n+1)^d\ge1$, we have $C(n+1)^d+1\le(C+1)(n+1)^d$, so this whole expression is bounded by a fixed constant times $(n+1)^d$. Finally, $(n+1)^d\le2^d(n^d+1)$ (succ_pow_le), putting the time bound in the defining form for polynomial time. The time-bound characterization then yields membership of the complement in P (mem_P_of_dtime_le).

**Key facts.** `Complexity.mem_P_iff`, `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`, `Complexity.succ_pow_le`, `Complexity.mem_P_of_dtime_le`.
