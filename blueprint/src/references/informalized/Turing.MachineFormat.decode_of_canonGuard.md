<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.decode_of_canonGuard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Short codes decode to fallback

**Claim.** If the paired encoding of $\alpha$ yields header $b$ and suffix $r$, and the suffix has length below the stated guard bound times one more than the value represented by $b$, then decoding $\alpha$ gives the fallback code.

**Proof.** The canonical guard block is the maximum of the format guard and the grammar bound. Compare these two quantities. If the format guard is the larger, the assumed length bound is below the format guard multiplied by one more than the header value, and the general short-guard decoding theorem (`decode_of_guard_lt`) gives the fallback. If the grammar bound is the larger, the same hypothesis is below the grammar bound multiplied by that factor, so the grammar-bound decoding theorem (`decode_of_grammar_guard`) gives the conclusion.

**Key facts.** `Turing.CodeFormat.decode_of_guard_lt`, `Turing.MachineFormat.decode_of_grammar_guard`.
