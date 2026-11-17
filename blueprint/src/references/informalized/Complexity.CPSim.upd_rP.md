<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.upd_rP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Position Register

**Claim.** Updating the input-position coordinate of the encoded assignment $(\rho,p,oc,tm)$ to $v$ yields the encoding $(\rho,v,oc,tm)$.

**Proof.** Compare the assignments at an arbitrary index. At index $R$, the update replaces the position value $p$ by $v$. At indices below $R$, both sides give the corresponding original register value; at index $R+1$ both give $oc$, and at index $R+2$ both give $tm$. Hence the assignments agree everywhere.
