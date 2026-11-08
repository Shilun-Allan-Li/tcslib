<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.anfCoeff_univ_eq_card_f₂OneSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Top coefficient and support parity

**Claim.** The algebraic normal form coefficient indexed by the full coordinate set equals the cardinality of the set of inputs where $f$ is $1$, interpreted in $\mathbb F_2$.

**Proof.** The coefficient at the full coordinate set is the sum of $f(x)$ over all inputs (`anfCoeff_univ_eq_sum_f₂BooleanFunction`). Since each value lies in $\mathbb F_2$, this sum is the cardinality, modulo two, of the inputs where the value is $1` (`sum_f₂BooleanFunction_eq_card_f₂OneSupport`). Combining these identities gives the result.

**Key facts.** `FABL.anfCoeff_univ_eq_sum_f₂BooleanFunction`, `FABL.sum_f₂BooleanFunction_eq_card_f₂OneSupport`.

**Caveat.** The supplied informal statement describes a degree-parity corollary; this account follows the formal statement and proof source.
