<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.isPivotal_iff_setCoordinate_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotality from coordinate values

**Claim.** A function is pivotal at $x$ in coordinate $i$ exactly when its values at the inputs obtained by setting coordinate $i$ to $+1$ and to $-1$ differ.

**Proof.** The coordinate $x_i$ is either $+1$ or $-1$. If it is $+1$, setting coordinate $i$ to $+1$ returns $x$, while flipping it gives the input obtained by setting it to $-1$. Thus pivotality is exactly inequality of the function's values at those two inputs. If $x_i=-1$, the roles are reversed: setting it to $-1$ returns $x$, and flipping it sets it to $+1$. The inequality is unchanged when its two sides are interchanged, giving the same criterion.

**Key facts.** `FABL.setCoordinate_eq_self`.
