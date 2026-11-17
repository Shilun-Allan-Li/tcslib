<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_mapSnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Second-Component Mapping

**Claim.** If $g$ is polynomial-time computable, then decoding an input as a pair $(a,b)$ and returning the encoding of $(a,g(b))$ when decoding succeeds, and the empty word otherwise, is polynomial-time computable.

**Proof.** Take a machine computing $g$ in time $C(n+1)^e$. The pair-mapping construction applies this machine to the second component and re-encodes the pair, giving a machine with time bound $K(n+1+C(n+1)^e)$ (`Turing.FinTM.computesFunInTime_pairMapSnd`); the time bound for $g$ is monotone, as required there. For $n+1\geq1$, both $n+1$ and $(n+1)^e$ are at most $(n+1)^{e+1}$. Therefore the bound is at most $K(C+1)(n+1)^{e+1}$, which is polynomial. The machine's computation may be allowed this larger bound by monotonicity of running-time witnesses (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_pairMapSnd`, `Turing.FinTM.ComputesInTime.mono`.
