<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStepPair_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired Shift Frame

**Claim.** At every zone $k$ distinct from $i-1$ and $i$, the paired shift at zone $i$ leaves both side words unchanged.

**Proof.** By definition, the paired shift applies the outward word shift to the left side and the inward word shift to the right side. Each word-shift definition changes entries only at indices $i-1$ and $i$. Since $k$ is distinct from both, its entry follows the unchanged branch in each definition, proving both equalities.
