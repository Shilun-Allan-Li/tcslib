<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinActiveCap_add_one_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Active cap bound with an additive one

**Claim.** For $0<\tau\le1$ and $C=\lceil4/\tau^2\rceil$, one has $C+1\le9/\tau^2$.

**Proof.** The active-cap estimate gives $C\le8/\tau^2$ (`FABL.goldreichLevinActiveCap_cast_le`). Since $0<\tau\le1$, we have $\tau^2\le1$, hence $1\le1/\tau^2$. Adding these bounds gives $C+1\le8/\tau^2+1/\tau^2=9/\tau^2$.

**Key facts.** `FABL.goldreichLevinActiveCap_cast_le`.
