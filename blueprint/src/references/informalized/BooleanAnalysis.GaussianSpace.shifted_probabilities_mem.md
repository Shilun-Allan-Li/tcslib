<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.shifted_probabilities_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interior of Shifted Probabilities

**Claim.** If $b\ge0$, $a-b>0$, $a+b<1$, and $0\le t\le b$, then both $a+t$ and $a-t$ belong to $(0,1)$.

**Proof.** From $t\ge0$ and $a-b>0$, we get $a+t>0$. From $t\le b$ and $a+b<1$, we get $a+t<1$. For the other shift, $t\le b$ and $a-b>0$ give $a-t>0$, while $t\ge0$ and $a+b<1$ give $a-t<1$. Thus both numbers lie strictly between zero and one.
