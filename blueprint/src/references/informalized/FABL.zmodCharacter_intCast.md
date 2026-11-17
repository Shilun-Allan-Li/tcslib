<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.zmodCharacter_intCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer formula for cyclic characters

**Claim.** For every positive integer $m$ and integers $j,x$, the cyclic character indexed by $j$ modulo $m$, evaluated at $x$ modulo $m$, equals $\exp\!\left(2\pi i\,\frac{jx}{m}\right)$.

**Proof.** Unfold the cyclic character as the character supplied by the standard additive equivalence between residues and characters. Its value at an integer representative is the circle-valued exponential with angle $2\pi jx/m$. Passing from the circle to its complex value gives the stated complex exponential. The remaining equality is the real-arithmetic identity rearranging the exponent into the displayed quotient.
