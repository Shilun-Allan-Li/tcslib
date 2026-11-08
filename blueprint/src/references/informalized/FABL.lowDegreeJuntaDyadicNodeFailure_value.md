<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaDyadicNodeFailure_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dyadic Node Failure Value

**Claim.** For natural numbers $k,b$, the dyadic node failure parameter has value $1/(T_k2^{b+1})$, where $T_0=1$ and $T_{j+1}=1+2T_j$.

**Proof.** Unfolding the node failure parameter, the per-call failure parameter, and the dyadic failure parameter identifies its value as $(1/2^{b+1})/T_k$. The call count $T_k$ is positive (the positivity result `juntaTreeCallCount_pos`), so the rational denominators are nonzero and the fractions can be combined. The result is $1/(T_k2^{b+1})$.

**Key facts.** `FABL.juntaTreePerCallFailure_value`, `FABL.lowDegreeJuntaDyadicFailure_value`, `FABL.juntaTreeCallCount_pos`.
