<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.seedWidthThreeCNF_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Converted formula size bound

**Claim.** If $3\le r$, the converted seed acceptance CNF has size at most $r2^r$.

**Proof.** The size bound for the width-three Tseitin conversion gives a size at most $(r-2)$ times the original formula's size, provided the chosen width is at least three and the original formula's width is no greater than that width (`FABL.widthThreeTseitin_size_le`). Here the chosen width is $r$, which meets the condition, and the original acceptance formula has width at most $r$ (`FABL.seedAcceptanceCNF_width_le`). Its size is at most $2^r$ (`FABL.seedAcceptanceCNF_size_le`), so the converted size is at most $(r-2)2^r$. Since $r-2\le r$, this is at most $r2^r$, the stated budget.

**Key facts.** `FABL.widthThreeTseitin_size_le`, `FABL.seedAcceptanceCNF_width_le`, `FABL.seedAcceptanceCNF_size_le`.
