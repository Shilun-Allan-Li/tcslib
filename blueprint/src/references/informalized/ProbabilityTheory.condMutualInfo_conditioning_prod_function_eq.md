<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_conditioning_prod_function_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redundant Deterministic Conditioning

**Claim.** Adding $f(Z)$ to the conditioning variable does not change the conditional mutual information of $X$ and $Y$.

**Proof.** The augmented variable $(Z,f(Z))$ is obtained from $Z$ by the map $z\mapsto(z,f(z))$. This map is injective, since its first component recovers $z$. Conditional mutual information is invariant under an injective recoding of the conditioning variable (`condMutualInfo_of_inj`), so conditioning on $(Z,f(Z))$ gives the same value as conditioning on $Z$.
