<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.fieldSize_le_two_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Field Size Bound by Twice the Scale

**Claim.** The field size satisfies $2^D\le 2S$.

**Proof.** The scale exceeds one, so the ceiling logarithm is positive, and the field degree equals this ceiling logarithm (\texttt{SmallBiasInput.fieldDegree\_eq\_clog}). The defining estimate for the ceiling logarithm gives $2^{(\lceil\log_2 S\rceil-1)}<S$ (\texttt{Nat.pow\_pred\_clog\_lt\_self}). Since the exponent is the predecessor of a positive integer, $D=(D-1)+1$, whence $2^D=2^{D-1}\cdot 2$. Multiplying the strict estimate by $2$ gives $2^D<2S$, and thus $2^D\le 2S$.

**Key facts.** `FABL.SmallBiasInput.fieldDegree_eq_clog`, `FABL.SmallBiasInput.one_lt_scale`.

**Caveat.** The proof also uses the natural-number ceiling-logarithm fact Nat.pow_pred_clog_lt_self, whose statement is not listed among the provided upstream lemmas.
