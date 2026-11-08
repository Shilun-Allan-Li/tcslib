<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairMapSnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapping the second pair component

**Claim.** If a finite Turing machine computes $g$ within a monotone time bound $T_g$, then another finite Turing machine maps a successfully parsed pair $(a,b)$ to the pair encoding of $(a,g(b))$, and returns the empty word if parsing fails, in time bounded by a constant times $|z|+1+T_g(|z|)$.

**Proof.** First extract the second component, using the empty word when parsing fails, and run the machine for $g$ on that extracted word. The catalog-payload construction combines these steps and bounds their time using the monotonicity of $T_g$ (`catalogPayload_computes`). Then apply the pair-mapping machine to encode the original first component together with the computed result; its time bound is a constant multiple of the preceding computation time plus the input length (`pairMap_computes`). On a failed parse the output is empty. On a successful parse, the extracted second component is exactly $b$, so the resulting output is the encoding of $(a,g(b))$. Combining the time bounds and enlarging the constant gives the stated form (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.catalogPayload_computes`, `Turing.FinTM.pairMap_computes`, `Turing.FinTM.ComputesInTime.mono`.
