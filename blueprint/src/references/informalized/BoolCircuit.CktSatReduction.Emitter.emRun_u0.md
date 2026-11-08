<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.emRun_u0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Argument Counter Update

**Claim.** In phase $u(k,0)$, processing $j$ consecutive true bits changes the first argument counter from $a$ to $a+j$, leaving the resulting run on the remaining input $r$ in phase $u(k,0)$.

**Proof.** Induct on $j$, generalizing $a$. The case $j=0$ is immediate. For the successor case, the next true bit in phase $u(k,0)$ keeps the machine in that phase and increments the first argument counter by one. The remaining $j$ bits then have the effect stated by the induction hypothesis, so the final counter is $(a+1)+j=a+(j+1)$; the rest of the run is on $r$.
