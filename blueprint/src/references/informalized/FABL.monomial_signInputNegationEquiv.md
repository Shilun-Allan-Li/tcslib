<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.monomial_signInputNegationEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial under Coordinate Sign Changes

**Claim.** Negating the coordinates selected by $\sigma$ multiplies the monomial on $S$ by the product of $-1$ over selected indices in $S$, with factor $1$ at the other indices.

**Proof.** Expand the monomial after the coordinate changes. For each $i\in S$, if $\sigma(i)$ is true, the input sign is negated, so its sign value is negated as well (`signValue_neg`); if $\sigma(i)$ is false, its sign value is unchanged. Thus each factor is the original sign value multiplied by $-1$ in the selected case and by $1$ otherwise. Combining these factors across $S$ yields the stated multiplier times the original monomial.

**Key facts.** `FABL.signValue_neg`.
