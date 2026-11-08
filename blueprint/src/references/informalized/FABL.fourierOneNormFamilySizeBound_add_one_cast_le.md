<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.fourierOneNormFamilySizeBound_add_one_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the family size

**Claim.** For $s\ge0$ and $0<\varepsilon\le1/2$, the integer $N=\max\{1,\lceil4s^2/\varepsilon\rceil\}$ satisfies $N+1\le6(s+1)^2/\varepsilon$.

**Proof.** Put $x=4s^2/\varepsilon$. Positivity of $\varepsilon$ and $s^2\ge0$ give $x\ge0$. The ceiling estimate gives $\lceil x\rceil\le x+1$, while $1\le x+1$; hence $N\le x+1$ and therefore $N+1\le x+2$. After multiplying by the positive $\varepsilon$, it remains to check $4s^2+2\varepsilon\le6(s+1)^2$. Using $2\varepsilon\le1$ and expanding the right side, this follows from $4s^2+1\le6s^2+12s+6$, which holds for $s\ge0$. The parameter bounds used here follow from `positiveLearningParameter_toReal_mem_Ioc`.

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`.
