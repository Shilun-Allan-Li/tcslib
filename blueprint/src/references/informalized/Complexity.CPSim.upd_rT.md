<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.upd_rT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Time Register

**Claim.** Updating the time-counter coordinate of the encoded assignment $(\rho,p,oc,tm)$ to $v$ yields the encoding $(\rho,p,oc,v)$.

**Proof.** Compare the assignments at an arbitrary index. The update changes the value at the final index $R+2$ from $tm$ to $v$. At index $R$ both assignments return $p$, at index $R+1$ both return $oc$, and below $R$ both return the corresponding value of $\rho$. Thus they agree at every index.
