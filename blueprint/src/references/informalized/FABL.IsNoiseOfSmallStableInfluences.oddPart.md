<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.IsNoiseOfSmallStableInfluences.oddPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Parts Preserve Noise Representations

**Claim.** The odd part of a bounded function that is a noise transform of a function with small stable influences is itself the noise transform of a bounded function with the same stable influence bound.

**Proof.** Choose a bounded function $f$ witnessing that $g$ is its noise transform and that each stable influence of $f$ at parameter $1-\varepsilon$ is at most $\varepsilon$. The odd part of a bounded function remains bounded, so $f$'s odd part is an admissible bounded witness. The noise operator commutes with taking odd parts: the odd part of the noise transform of $f$ equals the noise transform of the odd part of $f$ (`BoundedCubeFunction.noise_oddPart`). Finally, since $\varepsilon\in[0,1]$, the parameter $1-\varepsilon$ lies in $[0,1]$. Stable influence of the odd part is at most that of $f$ at this parameter (`stableInfluence_oddPart_le`), so every coordinate still has stable influence at most $\varepsilon$.

**Key facts.** `FABL.BoundedCubeFunction.noise_oddPart`, `FABL.stableInfluence_oddPart_le`.
