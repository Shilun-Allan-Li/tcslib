<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step configuration correspondence

**Claim.** A step of the transverse binary realization from the encoding of an original configuration equals the encoding of the original machine’s next configuration.

**Proof.** First split on the original configuration’s state. If it is halting, both machines remain at their current configurations, so the encoded configurations agree. Otherwise, write the state as $q$. The encoded configuration has the same state. The input-symbol decoding fact `Complexity.parallelCfg_input` ensures that the original transition sees the input symbol represented by the encoded machine’s input symbol. Likewise, `Complexity.parallelCfg_read` ensures that decoding the family of symbol-indexed work-tape tracks recovers the original work-tape symbols. Thus both transition rules select the same original action. Compare the resulting configurations field by field: the state is the action’s successor state; the input-head position agrees because the input lengths match and both apply the same movement; each encoded work-tape track is updated at the same head coordinate with the corresponding encoded written symbol, and elsewhere retains its prior value; the work-head positions agree because their movements are copied from the original action; and the outputs agree because the same optional output is appended after applying the bit encoding. Hence the next configurations are equal.

**Key facts.** `Complexity.parallelCfg_input`, `Complexity.parallelCfg_read`.
