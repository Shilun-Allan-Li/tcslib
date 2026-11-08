<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.copyGuide_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the Guide Origin

**Claim.** For every natural number $j>0$ and every integer coordinate $z$, the partial copy guide after $j$ cells has the origin mark at $z$ if and only if $z=0$.

**Proof.** Unfold the definition of the guide and consider its defining conditions. At $z=-1$ it assigns the interior mark, not the origin mark. At any other coordinate, it can assign the origin mark only when $0\le z<j$ and the coordinate itself is $0$, which gives the forward implication. Conversely, if $z=0$, then $z\ne-1$ and, since $j>0$, the inequalities $0\le z<j$ hold; the definition therefore assigns the origin mark.
