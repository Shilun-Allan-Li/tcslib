<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.flipCoordinate_flipCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping twice restores a vector

**Claim.** For every sign vector $x$ and coordinate $i$, flipping coordinate $i$ twice returns $x$.

**Proof.** A coordinate update sets coordinate $i$ to the specified value (`setCoordinate_apply_self`). Thus the first flip sets that coordinate to $-x_i$, and the second sets it to the negative of the current value, namely $-(-x_i)=x_i$. Every other coordinate is unchanged by either update, so the resulting vector is $x$.

**Key facts.** `FABL.setCoordinate_apply_self`.
