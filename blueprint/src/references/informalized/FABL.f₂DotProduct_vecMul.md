<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.f₂DotProduct_vecMul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dot product and matrix multiplication

**Claim.** For an $m\times n$ matrix $H$ over $\mathbb F_2$, vectors $\gamma\in\mathbb F_2^n$ and $y\in\mathbb F_2^m$ satisfy $\langle\gamma,yH\rangle=\langle H\gamma,y\rangle$.

**Proof.** By symmetry of the dot product, $\langle\gamma,yH\rangle=\langle yH,\gamma\rangle$. The matrix dot product identity says that this equals $\langle y,H\gamma\rangle$. A second use of symmetry gives $\langle H\gamma,y\rangle$, as required.
