<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.of_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics along a deterministic path

**Claim.** If a configuration reaches $(l',v',\text{no answer})$ along a finite run with every choice resolved as false, and the guard holds at every configuration before the endpoint, then probabilistic semantics with acceptance probability $p$ at the endpoint implies the same semantics at the starting configuration.

**Proof.** Unpack the reachability assumption: it provides a run length $T$, equality of the run's endpoint with $(l',v',\text{no answer})$, and the guard at every earlier time. The deterministic-path theorem (`Complexity.LogProg.PSem.of_areach`) applies to precisely these data and transfers the endpoint's probabilistic semantics to the starting configuration.

**Key facts.** `Complexity.LogProg.PSem.of_areach`.
