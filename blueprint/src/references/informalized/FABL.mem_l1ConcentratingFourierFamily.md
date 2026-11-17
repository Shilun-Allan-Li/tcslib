<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.mem_l1ConcentratingFourierFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentrating Fourier family membership

**Claim.** A coordinate set $S$ belongs to the family concentrating the Fourier coefficients of $f$ in the $1$-norm exactly when $\varepsilon\le \|\widehat f\|_1\,|\widehat f(S)|$.

**Proof.** By definition, the family consists of all coordinate sets in the universal family that satisfy this inequality. Since $S$ is already a coordinate set of the prescribed type, membership in the universal family is automatic; membership therefore reduces precisely to the displayed inequality.
