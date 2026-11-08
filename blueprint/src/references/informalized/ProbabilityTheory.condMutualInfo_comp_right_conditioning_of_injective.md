<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.condMutualInfo_comp_right_conditioning_of_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Injective Recoding

**Claim.** Injectively recoding the second variable and the conditioning variable leaves conditional mutual information unchanged.

**Proof.** Write conditional mutual information as $H[X\mid Z]+H[f(Y)\mid g(Z)]-H[(X,f(Y))\mid g(Z)]$. Since $g$ is injective, relabelling the conditioning variable by $g$ leaves conditional entropy unchanged (`condEntropy_of_injective'`). Since $f$ is injective, relabelling $Y$ by $f$ also leaves its conditional entropy given $Z$ unchanged (`condEntropy_comp_of_injective`), and the same holds for the pair $(X,Y)$: the map $(x,y)\mapsto(x,f(y))$ is injective. Thus the three entropy terms become $H[X\mid Z]$, $H[Y\mid Z]$, and $H[(X,Y)\mid Z]$, respectively. Their combination is $I[X:Y\mid Z]$, proving the equality.
