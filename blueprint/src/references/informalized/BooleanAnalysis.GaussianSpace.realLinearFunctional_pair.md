<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.realLinearFunctional_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear functional on a pair

**Claim.** Every continuous real-linear functional on $\mathbb R^2$ satisfies $L(x,y)=xL(1,0)+yL(0,1)$.

**Proof.** Write $(x,y)=x(1,0)+y(0,1)$. Linearity sends this sum to the sum of the images, and sends scalar multiples to the corresponding scalar multiples. Therefore $L(x,y)=xL(1,0)+yL(0,1)$.
