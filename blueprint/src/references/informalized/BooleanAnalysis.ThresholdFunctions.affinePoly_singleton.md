<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.affinePoly_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coefficient of an Affine Family

**Claim.** For $n\in\mathbb N$, $c\in\mathbb R$, $a\in\mathbb R^n$, and each coordinate $i$, the affine coefficient family has coefficient $a_i$ at the singleton set $\{i\}$.

**Proof.** The singleton $\{i\}$ is nonempty, so its coefficient is given by the sum over coordinates. In that sum, the singleton condition holds exactly for the term indexed by $i$; all other terms vanish. The sum is therefore $a_i$.
