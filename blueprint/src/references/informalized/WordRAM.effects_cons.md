<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effects_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Nonempty Instruction List

**Claim.** Applying the list beginning with instruction $i$ to memory $m$ is the same as first applying $i$ and then applying the remaining list $l$.

**Proof.** By the left-to-right fold defining the effect of a list, processing the first instruction $i$ transforms $m$ into $\mathrm{effect}(i,m)$. The remaining instructions are then processed starting from that resulting memory, giving $\mathrm{effects}(l,\mathrm{effect}(i,m))$.
