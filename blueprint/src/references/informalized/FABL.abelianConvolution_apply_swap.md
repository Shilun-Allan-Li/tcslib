<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.abelianConvolution_apply_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Convolution Average

**Claim.** For functions on a finite abelian group, the normalized convolution at $x$ is also the uniform average of $f(x-y)g(y)$ over $y\in G$.

**Proof.** Commutativity of convolution gives $f*g=g*f$ (`FABL.abelianConvolution_comm`). Apply the convolution-as-uniform-average formula (`FABL.abelianConvolution_apply`) to $g*f$ at $x$; this expresses it as the average of $g(y)f(x-y)$. Since complex multiplication is commutative, each summand equals $f(x-y)g(y)$, yielding the claimed formula.

**Key facts.** `FABL.abelianConvolution_comm`, `FABL.abelianConvolution_apply`.
