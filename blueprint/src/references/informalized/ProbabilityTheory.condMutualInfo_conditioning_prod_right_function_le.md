<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_conditioning_prod_right_function_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning on a Function of the Right Variable

**Claim.** Conditioning additionally on $f(Z,Y)$ cannot increase the conditional mutual information between $X$ and $Y$ given $Z$.

**Proof.** Conditional mutual information is symmetric in its two variables. Swap $X$ and $Y$ on both sides, so that the extra conditioning variable is a function of the right-hand variable in the left-variable formulation. The resulting inequality is the result that conditioning on $(Z,f(Z,X))$ cannot increase conditional mutual information (`condMutualInfo_conditioning_prod_left_function_le`), applied with the variables interchanged. Symmetry gives the stated inequality.

**Key facts.** `ProbabilityTheory.condMutualInfo_conditioning_prod_left_function_le`.
