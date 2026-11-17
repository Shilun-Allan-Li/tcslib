<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Congruence of Probabilistic Semantics

**Claim.** If a configuration has probabilistic semantics with parameter $p$ and $p=q$, then it has probabilistic semantics with parameter $q$.

**Proof.** Probabilistic semantics is a proposition whose termination component is independent of the parameter, while its probability component asserts equalities with that parameter. Transport the entire proof of probabilistic semantics along the equality $p=q$; this changes the parameter in those equalities and leaves the configuration, guard, and termination statement unchanged.
