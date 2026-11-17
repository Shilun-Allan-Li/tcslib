<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_conditioning_prod_left_function_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning on a Function of the Pair

**Claim.** Adding $f(Z,X)$ to the conditioning variable cannot increase $I[X:Y\mid Z]$.

**Proof.** Let $A=(Z,f(Z,X))$ and $XZ=(X,Z)$. Since $Z$ is the first component of $A$, conditioning on $A$ gives no greater entropy for $Y$ than conditioning on $Z$: $H[Y\mid A]\le H[Y\mid Z]$ by entropy monotonicity under a function (`condEntropy_comp_ge`). Next, $(X,A)$ is an injective recoding of $(X,Z)$: its components recover both $X$ and $Z$. Therefore $H[Y\mid(X,A)]=H[Y\mid(X,Z)]$ by invariance under injective recoding (`condEntropy_of_injective'`). Use symmetry to write each mutual information as $H[Y\mid\text{conditioning}]-H[Y\mid(X,\text{conditioning})]$. The second entropy terms agree, while the first satisfies the inequality just established, proving the claim.
