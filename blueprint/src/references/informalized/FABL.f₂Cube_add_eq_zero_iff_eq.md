<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.f₂Cube_add_eq_zero_iff_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Sum and Equality on the Binary Cube

**Claim.** For any two vectors $x,y\in\mathbb{F}_2^n$, their sum is zero if and only if $x=y$.

**Proof.** In the field with two elements, every element is its own additive inverse, so $-y=y$; applying this coordinate by coordinate gives the same identity for vectors. In any additive group, $x+y=0$ is equivalent to $x=-y$. Substituting $-y=y$ yields exactly $x=y$.
