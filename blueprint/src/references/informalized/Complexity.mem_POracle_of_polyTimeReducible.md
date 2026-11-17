<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.mem_POracle_of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Reductions and Oracle Time

**Claim.** If a language is polynomial-time many-one reducible to an oracle language, then it is decidable in polynomial time with oracle access to that language.

**Proof.** Choose a reduction machine $F$ that computes $f(x)$ within $C(|x|+1)^c$ steps and satisfies $x\in L$ exactly when $f(x)\in O$. The oracle-machine construction captures the computation of $F$ and copies its output to the query tape; its transition simulation is guaranteed by `Complexity.queryTM_agree`, and its initial configuration by `Complexity.queryTM_init`. The capture simulation theorem (`Turing.OracleTM.capture_reaches_qQuery`) shows that the oracle machine reaches its query state after some $u\le C(|x|+1)^c$ steps. At that point the query tape contains exactly $f(x)$, including when this is the empty string (`Turing.OracleTM.queryString_bufferTape`).

The two-step oracle-answer behavior (`Turing.OracleTM.runFrom_two_of_qQuery`), together with the specified yes/no transitions (`Complexity.queryTM_yes` and `Complexity.queryTM_no`), then halts and outputs the oracle's answer bit. By the reduction equivalence, this is exactly the indicator of membership in $L$. Thus the machine decides $L$ within $u+2$ steps. Since $(|x|+1)^c\ge1$, we have $u+2\le(C+2)(|x|+1)^c$. The elementary power estimate (`Complexity.succ_pow_le`) bounds this by $(C+2)2^c(|x|^c+1)$; the machine can be run for this full bound by time monotonicity (`Turing.FinOracleTM.ComputesInTime.mono`). This is a polynomial-time oracle bound, as required.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.OracleTM.capture_reaches_qQuery`, `Turing.OracleTM.queryString_bufferTape`, `Turing.OracleTM.runFrom_two_of_qQuery`, `Complexity.queryTM_yes`, `Complexity.queryTM_no`, `Complexity.succ_pow_le`, `Turing.FinOracleTM.ComputesInTime.mono`.
