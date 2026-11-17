<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleFrozenCall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frozen virtual call simulation

**Claim.** If the machine $C$ reaches its exit state with result word after $t$ steps, without reaching that state earlier, then its virtual-head simulation reaches the corresponding tagged configuration after $t$ steps and does not reach $(ex,true)$ earlier.

**Proof.** Apply the virtual-head run simulation theorem (`Turing.vhostEmitTM_runFrom`) to the initial configuration with tag true. It gives a tag $b$ such that the simulated run after $t$ steps is the virtual encoding of the original run, and the tag remains valid for the simulated input-head position. Substitute the assumed endpoint of the original run. Since the original input head stays at position $1$ on the empty input, its virtual tag at that endpoint must still be true; hence $b=true$, giving the claimed endpoint configuration. For any $s<t$, apply the same run simulation at time $s$. If the simulated state were $(ex,true)$, projecting its state component would show that the original run is in state $ex$ at time $s$, contrary to the no-earlier-exit hypothesis.

**Key facts.** `Turing.vhostEmitTM_runFrom`.
