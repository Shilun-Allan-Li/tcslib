<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.toV_rad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radius Component Lookup

**Claim.** The component of $S.\mathrm{toV}$ selected by $\mathrm{rad}(\mathrm{toPh}(\phi))$ is $S.s$ when $\phi$ is false and $S.s1$ when $\phi$ is true; equivalently, it equals $\mathrm{rr}(S,\phi)$.

**Proof.** Split on the Boolean $\phi$. If it is false, $\mathrm{toPh}(\phi)$ selects the first-search phase and $\mathrm{rad}$ selects register index $2$, whose component in $S.\mathrm{toV}$ is $S.s$. This is also the value of $\mathrm{rr}(S,\phi)$ in this case. If $\phi$ is true, the second-search phase selects register index $3$, whose component is $S.s1$, again exactly the value of $\mathrm{rr}(S,\phi)$.
