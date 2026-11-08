<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.freeLiteralPosition_coordinate_mem_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Literal Coordinates Lie in the Support

**Claim.** If position $j$ in the list of literals of $T$ is free under $\rho$, then the coordinate of the literal at that position belongs to the support of $T$.

**Proof.** The literal at position $j$ belongs to the list of literals of $T$, by the basic list-membership property of indexed access. Every literal in that list has its coordinate in the support of $T$ (\texttt{mem\_support\_of\_mem\_literals}). Applying this fact to the literal at position $j$ gives the desired inclusion; the freeness assumption is not needed for this implication.

**Key facts.** `FABL.DNFTerm.mem_support_of_mem_literals`.
