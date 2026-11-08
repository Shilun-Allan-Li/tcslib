<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return semantics

**Claim.** If state $l$ contains the instruction that returns $b$, then every guarded configuration $(l,v,\text{no answer})$ has probabilistic semantics with acceptance probability $1$ when $b$ is true and $0$ when $b$ is false.

**Proof.** First consider the halted configuration $(\text{halted},v,\text{answer }b)$. A halted configuration with answer $b$ has probabilistic semantics with the corresponding deterministic acceptance probability (\texttt{PSem.halted}). The return instruction takes $(l,v,\text{no answer})$ exactly to this halted configuration. The deterministic-step principle for probabilistic semantics (\texttt{PSem.det}) therefore transfers the halted configuration's semantics back across this one step, using the assumed guard at $(l,v,\text{no answer})$.

**Key facts.** `Complexity.LogProg.PSem.halted`, `Complexity.LogProg.PSem.det`.
