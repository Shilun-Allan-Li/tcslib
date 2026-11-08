<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.cfgCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration circuit size bound

**Claim.** The size of the configuration circuit is at most $n+2+(T+1)(k(2T+1)+|\ell|+3)K$, where $K$ is the maximum total width of the circuits used for the instruction kinds of the configuration computation.

**Proof.** The general program-circuit size bound is $n+2$ plus the program length times the largest total width among its instruction kinds (`BoolCircuit.progCircuit_size_le`). Apply it to the configuration program. Its length is $(T+1)\,\mathrm{cfgStride}(M,|\ell|,T)$ (`Complexity.length_cfgProg`), and the stride is $k(2T+1)+|\ell|+3$. Substituting these into the general bound gives the stated inequality, with the maximum instruction-kind width denoted by $K$.

**Key facts.** `BoolCircuit.progCircuit_size_le`, `Complexity.length_cfgProg`.
