<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AReach.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Guarded Reachability

**Claim.** If the run reaches $b$ from $a$ with $G$ holding at every configuration before reaching $b$, and $G$ implies $G'$, then it reaches $b$ from $a$ with $G'$ holding at every configuration before reaching $b$.

**Proof.** Take the same time $T$ witnessing reachability of $b$. The endpoint remains $b$. At each time $t<T$, the configuration satisfies $G$ by the reachability hypothesis, so it satisfies $G'$ by the assumed implication.
