<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Equivalent Propositions

**Claim.** For a fixed nondeterministic register machine, oracle, input, guard, and configuration, if the configuration satisfies the termination and acceptance semantics for $P$, and $P$ is logically equivalent to $Q$, then it satisfies those semantics for $Q$.

**Proof.** By definition, the semantics consist of termination together with the equivalence between acceptance and the stated proposition. Keep the termination assertion from the hypothesis unchanged. For the acceptance assertion, compose the given equivalence between acceptance and $P$ with the assumed equivalence $P\leftrightarrow Q$. This gives the required equivalence between acceptance and $Q$.
