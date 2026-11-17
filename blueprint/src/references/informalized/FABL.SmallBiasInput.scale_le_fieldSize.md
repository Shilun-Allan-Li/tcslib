<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.scale_le_fieldSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scale Bounded by Field Size

**Claim.** The scale satisfies $S\le 2^D$.

**Proof.** The field degree equals the ceiling logarithm of the scale (\texttt{SmallBiasInput.fieldDegree\_eq\_clog}). By the defining property of the ceiling logarithm, $S\le 2^{\lceil\log_2 S\rceil}$. Substituting the field degree for this exponent proves $S\le 2^D$.

**Key facts.** `FABL.SmallBiasInput.fieldDegree_eq_clog`.
