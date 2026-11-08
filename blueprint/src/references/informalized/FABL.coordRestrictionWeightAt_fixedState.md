<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionWeightAt_fixedState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight of a fixed sign state

**Claim.** For any real $\delta$ and sign $s\in\{\pm1\}$, the weight of the restriction fixing a coordinate to $s$ is $(1-\delta)/2$.

**Proof.** Every sign is either $1$ or $-1$. In the first case the fixed-state restriction is `fixOne`, and in the second it is `fixNegOne`. By definition, both fixed restrictions have coordinate weight $(1-\delta)/2$, so the result holds in either case.
