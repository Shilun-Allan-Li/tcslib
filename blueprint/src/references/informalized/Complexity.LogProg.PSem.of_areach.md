<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.of_areach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics along a deterministic path

**Claim.** If the configuration at $l'$ with register valuation $v'$ and no answer has probabilistic semantics with acceptance probability $p$, then any configuration that reaches it by a finite run with every choice resolved as false also has that semantics, provided the guard holds at every configuration before the end of the run.

**Proof.** Proceed by induction on the run length $T$, using the stated false-choice deterministic simulation.

1. If $T=0$, the run ends where it starts. The endpoint assumption directly gives the desired semantics.
2. Suppose $T+1$ steps reach the endpoint. A halted starting configuration cannot do so: halted configurations remain fixed, whereas the endpoint is live. For a live start, inspect its first deterministic step. The exhaustive step classification (`Complexity.LogProg.astep_cases`) says this step either reaches another live configuration or halts with an answer. The latter case is impossible, since halted configurations remain fixed and cannot become the specified live endpoint. The same classification, together with the run endpoint, ensures the starting answer is absent: deterministic steps preserve the answer until a halting step, and a halted configuration cannot reach the live endpoint.
3. The first instruction cannot be a nondeterministic choice. In the false-choice deterministic simulation, a choice is replaced by an instruction that returns false immediately (`Complexity.LogProg.NARM.detPart_choose`), which would halt and hence could not reach the live endpoint. Thus the first instruction is deterministic. Its actual successor in the nondeterministic machine is the same as its successor in the false-choice simulation; this is the correspondence between deterministic instructions and a nondeterministic step (`Complexity.LogProg.nastep_det`, `Complexity.LogProg.nastep_det'`).
4. The guard holds at the starting configuration by the path hypothesis. Apply deterministic-step preservation (`Complexity.LogProg.PSem.det`) to the first instruction. Its successor reaches the same endpoint in the remaining $T$ steps, and the guard holds at each of those intermediate configurations by the original path hypothesis. The induction hypothesis gives probabilistic semantics at that successor, so preservation gives it at the start.

**Key facts.** `Complexity.LogProg.astep_cases`, `Complexity.LogProg.NARM.detPart_choose`, `Complexity.LogProg.nastep_det`, `Complexity.LogProg.nastep_det'`, `Complexity.LogProg.PSem.det`.
