<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_comp_right_le_of_comp_conditioning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Data Processing in the Second Variable

**Claim.** Replacing $Y$ by a function of $(Z,Y)$ cannot increase its conditional mutual information with $X$ given $Z$.

**Proof.** Conditional mutual information is symmetric in its two variables. Swap the two arguments on both sides, obtaining the claim that applying the map $(z,y)\mapsto f(z)(y)$ to the left variable $Y$ cannot increase its conditional mutual information with $X$ given $Z$. This is precisely conditional data processing for a function of the left variable (`condMutualInfo_comp_left_le_of_comp_conditioning`). Symmetry then gives the desired inequality in the original order.

**Key facts.** `ProbabilityTheory.condMutualInfo_comp_left_le_of_comp_conditioning`.
