<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ncompileTM_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Initial Configuration

**Claim.** The compiled nondeterministic machine's initial configuration on $x$ is obtained by adjoining blank auxiliary tapes to the initial arithmetic configuration at $l_0$, with all registers zero and the output empty.

**Proof.** The initial configuration of the register machine at label $l_0$ is exactly the arithmetic configuration represented by $\mathrm{aseam}\;x\;l_0\;(\lambda r.0)\;[]$ (the initial-configuration identification, `Complexity.LogProg.init_eq_aseam`). The compiled machine's initial configuration is the result of adjoining blank auxiliary tapes to the initial configuration of its underlying deterministic compilation (the seam-initialization fact, `Complexity.LogProg.seam_init`). Applying that fact to the deterministic program used in the compilation, and using the initial-configuration identification, gives the stated equality.

**Key facts.** `Complexity.LogProg.init_eq_aseam`, `Complexity.LogProg.seam_init`.
