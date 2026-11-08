<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.upd_rg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating an Original Register

**Claim.** Updating original register $r$ to $v$ in the extended assignment $(\rho,p,oc,tm)$ agrees with first updating $r$ in $\rho$ and leaving the three auxiliary coordinates unchanged.

**Proof.** Evaluate both assignments at an arbitrary index in the extended register file. For an index below $R$, it represents an original register, and the update there agrees exactly with updating that register in $\rho$. At the three auxiliary indices $R$, $R+1$, and $R+2$, the original-register update has no effect, so both sides retain respectively $p$, $oc$, and $tm$. Therefore the two assignments coincide everywhere.
