<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PolytimeMap.comp_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Application of Composed Maps

**Claim.** For polynomial-time maps $F$ and $G$ on Boolean lists, their composition sends any Boolean list $x$ to $G(F(x))$.

**Proof.** By definition, the composed map has underlying function $G\circ F$. Evaluating this function at $x$ gives $G(F(x))$, as claimed.
