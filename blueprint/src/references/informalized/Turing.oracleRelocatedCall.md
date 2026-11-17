<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleRelocatedCall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relocating a Finite-Machine Call

**Claim.** A finite-machine computation that reaches state $ex$ with the result word after $t$ steps, and does not reach $ex$ earlier, is reproduced by its embedded virtual-host simulation: it reaches the corresponding embedded result configuration after $t$ steps and does not reach tagged state $(ex,\mathrm{true})$ earlier.

**Proof.** First apply the virtual-host simulation result (`Turing.oracleFrozenCall`): it transfers the finite-machine run and its first-arrival condition to the virtual-host configuration, preserving the indicated input position and output. Then use the step-by-step embedding identity (`Turing.embedEmitTM_runFrom`), which says that running the embedded emitting machine from the embedded configuration yields the embedding of the virtual-host run at the same time. Rewriting the endpoint with this identity gives the claimed embedded result configuration. Rewriting each earlier-time configuration the same way transfers the virtual-host nonarrival conclusion to the embedded machine.

**Key facts.** `Turing.oracleFrozenCall`, `Turing.embedEmitTM_runFrom`.
