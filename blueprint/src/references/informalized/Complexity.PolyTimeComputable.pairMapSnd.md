<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.PolyTimeComputable.pairMapSnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time payload map

**Claim.** For polynomial-time computable $g$, the function that sends a valid encoding of $(a,b)$ to the encoding of $(a,g(b))$, and sends an invalid encoding to the empty string, is polynomial-time computable.

**Proof.** Take a machine computing $g$ in time $C(|z|+1)^c$. Its time bound is monotone, so the pair-map construction applies: it produces a machine for the stated operation that runs in time $K(|x|+1+T_g(|x|))$ for some constant $K$, where $T_g(n)=C(n+1)^c$. Thus the time is bounded by $K(|x|+1+C(|x|+1)^c)$. For $n=|x|$, both $n+1$ and $(n+1)^c$ are at most $(n+1)^{c+1}$; consequently the displayed bound is at most $K(C+1)(n+1)^{c+1}$. The machine computes the required function by the pair-map construction (`Turing.FinTM.computesFunInTime_pairMapSnd`), and increasing its time allowance to this polynomial bound preserves its computation (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_pairMapSnd`, `Turing.FinTM.ComputesInTime.mono`.
