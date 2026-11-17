<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterSteps.lean :: Complexity.UTab.lstart_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor start-record identity

**Claim.** For the start record at step $t+1$, replacing its $q$-coordinate by $(t+1)S-S$ leaves the record unchanged.

**Proof.** The record’s $q$-coordinate is defined to be $0$ when its step parameter is zero, and otherwise to be the step parameter times $S$ minus $S$. At step $t+1$, split on whether $t=0$. If $t=0$, then $t+1=1$, so both the defined coordinate and the proposed replacement are $0$. If $t\ne0$, the defined coordinate is exactly $(t+1)S-S$, the proposed value. Every other coordinate is unchanged by the record update, so the two records are equal.
