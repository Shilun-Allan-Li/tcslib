<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.emRun_u1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Argument Counter Update

**Claim.** In phase $u(k,1)$, processing $j$ consecutive true bits changes the second argument counter from $b$ to $b+j$, leaving the resulting run on the remaining input $r$ in phase $u(k,1)$.

**Proof.** Induct on $j$, generalizing $b$. The case $j=0$ is immediate. For the successor case, the next true bit in phase $u(k,1)$ keeps the machine in that phase and increments the second argument counter by one. The induction hypothesis processes the remaining $j$ bits, giving the final counter $(b+1)+j=b+(j+1)$ and leaving the run on $r$.
