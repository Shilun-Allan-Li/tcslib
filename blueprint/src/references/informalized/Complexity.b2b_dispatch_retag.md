<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_dispatch_retag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retagging a Machine State

**Claim.** Mapping the state of a configuration to $(j,q)$ agrees with first mapping it to $q$ and then mapping that state to $(j,q)$.

**Proof.** A configuration's state is either absent, representing a halted configuration, or present. In the absent case both state maps leave it absent, and every other component of the configuration is unchanged. In the present case, mapping the state directly gives $(j,q)$; mapping first to $q$ and then to the pair gives the same state. All non-state components are unchanged in both constructions, so the configurations agree.
