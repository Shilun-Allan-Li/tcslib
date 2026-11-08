<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runtime scale factor bounds

**Claim.** The runtime scale $R$ is at least one, and it bounds $n+1$, $s+1$, and $1/\varepsilon$ from above.

**Proof.** Write $x=n+1$, $y=s+1$, and let $\varepsilon$ be the learning parameter viewed as a real number. Since $n,s$ are nonnegative, $x,y\ge1$. The learning parameter lies in $(0,1/2]$ (`positiveLearningParameter_toReal_mem_Ioc`), so in particular $0<\varepsilon\le1$. Thus $xy\ge1$, giving $1\le xy/\varepsilon=R$. Also $y\ge1$ and $1/\varepsilon\ge1$, so $x\le xy/\varepsilon$; likewise $y\le xy/\varepsilon$. Finally, $xy\ge1$ gives $1/\varepsilon\le xy/\varepsilon$. These are exactly the three factor bounds.

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`.
