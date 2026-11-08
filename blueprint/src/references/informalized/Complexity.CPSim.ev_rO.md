<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.ev_rO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the Output Register

**Claim.** For the extended assignment, evaluation at the distinguished output-counter register returns $oc$.

**Proof.** The output-counter register has index $R+1$. This index is not less than $R$, so the first branch in the definition of the extended assignment does not apply; it is exactly $R+1$, so the next matching branch returns $oc$.
