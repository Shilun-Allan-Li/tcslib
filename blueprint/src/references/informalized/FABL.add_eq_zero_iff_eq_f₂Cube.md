<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.add_eq_zero_iff_eq_f₂Cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition in the Boolean Cube

**Claim.** For every natural number $n$ and all $x,y\in\mathbb{F}_2^n$, $x+y=0$ if and only if $x=y$.

**Proof.** In the Boolean cube, every coordinate is its own additive inverse: $-y=y$. Indeed, this holds coordinatewise because negation is the identity modulo two. In any additive group, $x+y=0$ is equivalent to $x=-y$. Substituting $-y=y$ gives exactly $x=y$.
