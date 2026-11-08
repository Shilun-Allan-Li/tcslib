<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the first input bit

**Claim.** One parsing step reads the first input bit $b$, advances the input head from $|pre|+1$ to $|pre|+2$, and stores $b$ as the pending bit without changing the buffers, work-head positions, or output.

**Proof.** At input position $|pre|+1$, the configuration reads the list entry indexed by $|pre|$ (`a2_mapCfg_read`); the decomposition $x=pre\mathbin{++}[b]\mathbin{++}rest$ makes this entry $b$. The parsing rule for a present input bit moves right, leaves both work tapes and their heads unchanged, emits nothing, and enters the parsing state with $b$ pending. The action-to-configuration calculation (`a2_map_move`) gives these unchanged buffers, heads, and output together with the moved input position. Since this position is not the right boundary, a positive input movement advances it by exactly one (`moveInputPos_pos_of_ne_right`), yielding $|pre|+2$.

**Key facts.** `Turing.FinTM.a2_mapCfg_read`, `Turing.FinTM.a2_map_move`, `Turing.moveInputPos_pos_of_ne_right`.
