<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.n_le_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension Bounded by the Scale

**Claim.** The dimension satisfies $n\le S$.

**Proof.** From $2a\le b$ and $a>0$, we have $a\le b$. Multiplying by the positive dimension gives $an\le nb$. The defining ceiling-division property of $S=\lceil nb/a\rceil$ gives $nb\le aS$. Therefore $an\le aS$; since $a>0$, cancellation yields $n\le S$.
