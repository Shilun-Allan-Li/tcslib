<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.inputBlock_flipCoordinate_of_ne_tribe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unaffected input blocks

**Claim.** If coordinate $i$ belongs to a block different from $t$, flipping $i$ leaves block $t$ unchanged.

**Proof.** To prove equality of the two blocks, compare their entries at an arbitrary position $o\in\mathrm{Fin}(w)$. The coordinate corresponding to $(t,o)$ cannot be $i$: otherwise applying the inverse coordinate-pairing equivalence would identify $(t,o)$ with the pair for $i$, contradicting that their block indices differ. Thus the flip updates a different coordinate, so the entry at the coordinate corresponding to $(t,o)$ is unchanged. Since this holds for every $o$, the blocks are equal.
