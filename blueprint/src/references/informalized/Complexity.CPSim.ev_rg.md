<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.ev_rg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values at Original Registers

**Claim.** For every original register $r<R$, the extended assignment gives it the value $\rho(r)$.

**Proof.** The embedding of the original register indices into the extended register set preserves the index $r$. Since $r<R$, the first case in the definition of the extended assignment applies, and it evaluates to $\rho(r)$.
