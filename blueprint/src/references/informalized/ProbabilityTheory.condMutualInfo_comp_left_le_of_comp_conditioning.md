<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_comp_left_le_of_comp_conditioning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Data Processing

**Claim.** If $W$ is obtained from $X$ by a map that may depend on the conditioning variable $Z$, then $I[W:Y\mid Z]\le I[X:Y\mid Z]$.

**Proof.** First adjoin $Z$ to $X$. The pair $(Z,X)$ is an injective recoding of $X$ when the conditioning variable is already fixed, so this does not change the conditional mutual information. Now apply conditional data processing for a function of the left variable: applying $(z,x)\mapsto f(z)(x)$ to $(Z,X)$ cannot increase its conditional mutual information with $Y$ given $Z$. Combining these two statements gives the inequality.
