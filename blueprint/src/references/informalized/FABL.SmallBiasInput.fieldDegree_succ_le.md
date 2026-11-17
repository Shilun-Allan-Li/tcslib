<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.fieldDegree_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Field Degree

**Claim.** For the scale $S$ and field degree $D$, one has $D+1\le 4(S+1)$.

**Proof.** The elementary bound that every natural number $m$ satisfies $m\le 2^m$ (\texttt{nat\_succ\_le\_two\_pow\_succ}) gives $D+1\le 2^{D+1}$. Since $2^{D+1}=2^D\cdot 2$ and the field-size estimate gives $2^D\le 2S$ (\texttt{SmallBiasInput.fieldSize\_le\_two\_scale}), it follows that $2^{D+1}\le (2S)\cdot 2=4S$. In particular, $4S\le 4(S+1)$, proving the asserted bound.

**Key facts.** `FABL.nat_succ_le_two_pow_succ`, `FABL.SmallBiasInput.fieldSize_le_two_scale`.
