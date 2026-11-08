<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.upd_rO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Output Register

**Claim.** Updating the output-counter coordinate of the encoded assignment $(\rho,p,oc,tm)$ to $v$ yields the encoding $(\rho,p,v,tm)$.

**Proof.** Compare the two assignments at an arbitrary register index. Updating changes the value only at the output-register index $R+1$, where the result is $v$. At indices below $R$, both assignments return the corresponding value of $\rho$; at index $R$ both return $p$; and at the final index $R+2$ both return $tm$. These cases exhaust the $R+3$ indices and establish equality of the assignments.
