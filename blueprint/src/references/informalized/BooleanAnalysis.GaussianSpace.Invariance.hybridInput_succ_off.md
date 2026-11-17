<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.hybridInput_succ_off -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consecutive hybrids agree off one coordinate

**Claim.** For $j\ne i$, the hybrid inputs at stages $i$ and $i+1$ agree at coordinate $j$.

**Proof.** The inequality $j\ne i$ implies their natural-number values differ. Since $j$ is a natural number, it cannot lie between $i$ and $i+1$; consequently $j<i$ holds exactly when $j<i+1$ holds. The rule selecting the left or right copy therefore chooses the same summand for $j$ at both stages, and both hybrid inputs return the same function there.
