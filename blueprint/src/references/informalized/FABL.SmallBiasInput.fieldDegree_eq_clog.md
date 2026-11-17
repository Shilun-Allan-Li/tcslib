<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.fieldDegree_eq_clog -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field Degree and Logarithmic Scale

**Claim.** For a small-bias input, the field degree equals the base-$2$ ceiling logarithm of its scale.

**Proof.** The scale is greater than $1$ (`SmallBiasInput.one_lt_scale`). Hence its base-$2$ ceiling logarithm is positive, so it is at least $1$. The field degree is the maximum of $1$ and that logarithm; because the logarithm is already at least $1$, the maximum is the logarithm itself.

**Key facts.** `FABL.SmallBiasInput.one_lt_scale`.
