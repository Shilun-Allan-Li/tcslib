<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinActiveCap_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Active cap bound

**Claim.** For $0<\tau\le1$ and $C=\lceil4/\tau^2\rceil$, one has $C\le8/\tau^2$.

**Proof.** The threshold assumptions imply $\tau^2\le1$, so $1/2\le4/\tau^2$. The ceiling estimate that a ceiling is at most twice its argument when the argument is at least $1/2$ therefore gives $C\le2(4/\tau^2)=8/\tau^2$.
