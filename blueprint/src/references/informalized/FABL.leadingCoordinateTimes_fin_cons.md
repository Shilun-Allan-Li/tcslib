<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.leadingCoordinateTimes_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading-coordinate product

**Claim.** For a Boolean function $g$ on the $n$-dimensional sign cube, a sign $b$, and an input $x$, the leading-coordinate product evaluated at $(b,x)$ is $b g(x)$.

**Proof.** By definition, the leading-coordinate product at an input $y$ is its first coordinate multiplied by $g$ evaluated on the remaining coordinates. For $y=(b,x)$, the first coordinate is $b$ and the remaining-coordinate function is exactly $x$. Substitution gives $b g(x)$.
