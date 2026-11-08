<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.DTIMEAdvice_eq_empty_of_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Time Advice Classes Are Empty

**Claim.** If $T(0)=0$, then $\mathrm{DTIMEAdvice}(T,a)$ is empty for every advice-length function $a$.

**Proof.** Suppose a language belonged to this class, witnessed by a constant, an advice function, and a machine. Apply its decision guarantee to the empty input. The time bound there is the witness constant times $T(0)$, hence zero. By the characterization of computation within time (`Turing.FinTM.computesInTime_iff`), the machine’s run at that time must already be in a halting state. But a machine’s initial configuration has its designated initial state, which is present as `some` state; at zero steps the run is still that initial configuration. It therefore cannot have state `none`, a contradiction. No language lies in the class, so it equals the empty set.

**Key facts.** `Turing.FinTM.computesInTime_iff`.
