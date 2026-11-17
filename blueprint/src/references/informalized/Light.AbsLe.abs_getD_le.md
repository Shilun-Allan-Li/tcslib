<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: Light.AbsLe.abs_getD_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Defaulted List Entry

**Claim.** If every entry of an integer list $l$ has absolute value at most $U$, and $0\le U$, then every defaulted entry $l_i^{(0)}$, with default value zero, also has absolute value at most $U$.

**Proof.** Apply the fact that a list lookup with a default preserves any property shared by the default value and every list entry (`List.getD_of_forall_mem`). Here the property is $|x|\le U$: it holds for every entry by assumption, and for the default value $0$ because $|0|=0\le U$. Thus it holds for the lookup at every index.

**Key facts.** `List.getD_of_forall_mem`.
