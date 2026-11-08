<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenLoop.lean :: Complexity.LogProg.ISGen.ghalf_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving the input-length register

**Claim.** If the registers of $\sigma$ are bounded by $B$, $\sigma.lg+\operatorname{size}(\sigma.n)\le B$, and the round state with $n=0$ and $lg=\sigma.lg+\operatorname{size}(\sigma.n)$ has the asserted termination, register-bound, and acceptance property, then the same property holds from the halving-test state with registers $\sigma$.

**Proof.** Prove the claim by strong induction on the value of the input-length register, generalizing the register state subject to the stated bounds and the equality fixing that value. If $\sigma.n=0$, the zero test takes its positive branch directly to the round state. The resulting state agrees with the assumed one, so the semantic conclusion transfers by state equality (`IG.of_eq`). If $\sigma.n\ne0$, the zero test takes its negative branch; the machine halves $n$ and increments $lg$. The size-of-half identity says $\operatorname{size}(n)=\operatorname{size}(n/2)+1$ for nonzero $n$ (`Complexity.LogProg.ISCount.size_half`). Thus the new value of $lg$ is precisely the value required for the induction hypothesis at the strictly smaller register value $n/2$. The register bounds and the inequality on $lg+\operatorname{size}(n)$ are preserved, and the assumed round-state computation is transferred to the state required by the induction hypothesis using equality of states (`IG.of_eq`). Applying that hypothesis proves the result after the half and increment operations. In both branches, the machine-step semantic principles for zero tests, halving, and incrementing lift the downstream property back to the original state (`NSem.jz_pos`, `NSem.jz_neg`, `NSem.half`, and `NSem.inc`).

**Key facts.** `Complexity.LogProg.ISCount.size_half`, `Complexity.LogProg.ISGen.IG.of_eq`, `Complexity.LogProg.NSem.jz_pos`, `Complexity.LogProg.NSem.jz_neg`, `Complexity.LogProg.NSem.half`, `Complexity.LogProg.NSem.inc`.
