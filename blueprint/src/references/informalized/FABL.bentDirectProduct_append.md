<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.bentDirectProduct_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bent direct product on concatenated inputs

**Claim.** Evaluating the bent direct product at the concatenation of $x$ and $y$ gives $f(x)g(y)$.

**Proof.** By definition, the bent direct product at a vector $z$ is the product of $f$ evaluated on the first block of $(\mathrm{appendEquiv})^{-1}(z)$ and $g$ evaluated on its second block. For $z$ equal to the concatenation of $x$ and $y$, these two blocks are exactly $x$ and $y$. The value is therefore $f(x)g(y)$.
