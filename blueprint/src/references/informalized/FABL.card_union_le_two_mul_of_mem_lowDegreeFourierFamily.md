<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Union Size of Low-Degree Sets

**Claim.** If $S$ and $T$ each have at most $m$ elements, then $|S\cup T|\le 2m$.

**Proof.** The union has cardinality at most $|S|+|T|$. Membership in the low-degree family means each set has cardinality at most $m$ (`mem_lowDegreeFourierFamily`), so their sum is at most $m+m=2m$.

**Key facts.** `FABL.mem_lowDegreeFourierFamily`.
