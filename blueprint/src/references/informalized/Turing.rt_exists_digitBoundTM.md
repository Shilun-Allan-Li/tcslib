<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_exists_digitBoundTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded digit-writing machine

**Claim.** The digit-writing machine can be embedded into arbitrary surrounding tapes and output, retaining its bounds and producing the embedded endpoint with the binary expansion of $|x|+1$ on tape $\iota(0)$.

**Proof.** Start from the digit-writing machine given by `rt_exists_boundTM`. Lift its Boolean alphabet through the injection into the recursive symbol alphabet, obtaining a machine that performs the same computation with digit symbols. The run-lifting identity (`MultiTapeTM.liftSymbols_runFrom`) makes this correspondence exact at every time. For the embedded run, the run-embedding identity (`embedEmitTM_runFrom`) identifies each configuration with the embedding of the lifted configuration. Thus the original first-exit guarantee transfers directly. On selected tapes, the selected-position identity (`embedEmitCfg_selected_pos`) transfers the radius bound from the original computation. On tapes outside the embedding, the frame property (`embedEmitTM_frame`) keeps the heads fixed, giving zero displacement. The original endpoint writes the bits of $|x|+1$ on tape 0; lifting maps each bit to its digit symbol, and the embedding places that tape at index $\iota(0)$. The embedding therefore gives the claimed endpoint, including the unchanged surrounding data and prefixed output.

**Key facts.** `Turing.rt_exists_boundTM`, `Turing.MultiTapeTM.liftSymbols_runFrom`, `Turing.embedEmitTM_runFrom`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
