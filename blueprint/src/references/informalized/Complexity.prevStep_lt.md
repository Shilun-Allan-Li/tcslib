<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.prevStep_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Earlier block index

**Claim.** If $t$ is nonzero, $a<(t-1+1)\,\mathrm{cfgStride}(M,|\ell|,T)$, and $t\,\mathrm{cfgStride}(M,|\ell|,T)\le i$, then $a<i$.

**Proof.** Since $t\ne0$, natural-number subtraction satisfies $(t-1)+1=t$. The first hypothesis therefore gives $a<t\,\mathrm{cfgStride}(M,|\ell|,T)$, while the second bounds that quantity above by $i$. Transitivity yields $a<i$.
