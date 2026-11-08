<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric pair contraction

**Claim.** Under the stated continuity, nonnegativity, and two-point hypotheses on $P$, one has $L(t,(tb)^2)\le L(1,b^2)$ whenever $a+b,a-b,t\in[0,1]$.

**Proof.** Apply the endpoint comparison to the same $a,b,t,u,v$ with clock parameter $c=(tb)^2$, which is nonnegative. It gives $L(t,(tb)^2)\le L(1,(tb)^2+b^2(1-t^2))$. Since $(tb)^2+b^2(1-t^2)=b^2$, the right side is exactly $L(1,b^2)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_le_endpoint`.
