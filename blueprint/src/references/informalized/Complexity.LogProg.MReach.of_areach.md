<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.of_areach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting register-machine reachability to memory

**Claim.** A finite run of the deterministic part of a memory machine, ending at a live configuration and satisfying $G$ before the endpoint, lifts to a run of the memory machine with the memory tape and head fixed at $\mu$, and with both the register invariant and this fixed-memory condition holding before the endpoint.

**Proof.** Let $T$ witness the register-machine reachability. The final register configuration is live, so the simulation identity (\texttt{Complexity.LogProg.mrun_eq_arun}) applies through time $T$: at every time $t\leq T$, the memory-machine run from $(a,\mu)$ has register component equal to the register-machine run and memory component still equal to $\mu$. In particular, at $T$ its endpoint is $(a',\mu)$. For each $t<T$, the register reachability invariant supplies $G$ for the corresponding register configuration, while the simulation identity supplies the unchanged memory component. These are precisely the two parts of the lifted invariant.

**Key facts.** `Complexity.LogProg.mrun_eq_arun`.
