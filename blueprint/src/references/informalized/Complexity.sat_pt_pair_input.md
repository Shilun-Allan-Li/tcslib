<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_pair_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Pairing with the Input

**Claim.** If $f$ is polynomial-time computable, then the function sending $x$ to the pair encoding of $f(x)$ and $x$ is polynomial-time computable.

**Proof.** Take a machine computing $f$ within time $C(|x|+1)^e$. The pairing machine supplied by the pairing construction computes $\operatorname{pairEncode}(f(x),x)$ within $4C(|x|+1)^e+2|x|+8$ steps (`satPair_computes`). This is bounded by a polynomial of the required form: since $|x|+1\ge 1$, we have $(|x|+1)^e\le(|x|+1)^{e+1}$ and $|x|+1\le(|x|+1)^{e+1}$. Thus the displayed running time is at most $(4C+10)(|x|+1)^{e+1}$. Increasing a machine's allowed time preserves its computation (`ComputesInTime.mono`), so this polynomial bound witnesses the claim.

**Key facts.** `Complexity.satPair_computes`, `Turing.FinTM.ComputesInTime.mono`.
