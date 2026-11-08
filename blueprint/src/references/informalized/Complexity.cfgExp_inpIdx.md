<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgExp_inpIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-position index expansion

**Claim.** At the index assigned to time $t$ and input position $p<|\ell|+2$, the configuration expansion equals the input-position expansion for $M,w,t,p$.

**Proof.** The indexing lemma identifies this index's configuration position as $(t,p)$ in the input region (`Complexity.cfgPos_inpIdx`), using the bound $p<|\ell|+2$. At an input position, the definition of the configuration expansion returns the corresponding input-position expansion. This gives the claimed equality.

**Key facts.** `Complexity.cfgPos_inpIdx`.
