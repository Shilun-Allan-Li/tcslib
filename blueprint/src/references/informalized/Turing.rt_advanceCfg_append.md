<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_advanceCfg_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consecutive Tape Writes

**Claim.** Advancing by $u$, renaming states, and then advancing by $v$ gives the same configuration as renaming the original state and advancing by $u\mathbin{++}v$.

**Proof.** Compare the configuration fields. The final state is $r$ in either construction, while the input head and output are unchanged by these advance operations. For the selected tape, the two writes occupy consecutive intervals; the adjacent-write identity shows that they agree with one write of $u\mathbin{++}v$. Other tapes are untouched in both constructions. The selected head is advanced first by $|u|$ and then by $|v|$, which equals an advance by $|u|+|v|=|u\mathbin{++}v|$. Hence all fields agree.

**Key facts.** `Turing.rt_adjacentWrites`.
