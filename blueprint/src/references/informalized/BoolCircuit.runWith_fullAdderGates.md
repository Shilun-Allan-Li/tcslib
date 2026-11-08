<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.runWith_fullAdderGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outputs of a full-adder circuit

**Claim.** Executing the full-adder gate list appends the stated nine intermediate and output values to the input list.

**Proof.** Replace $L$ by the length of the input list using the length hypothesis. The full-adder list consists of two XOR gate blocks followed by one OR gate, so split execution along these concatenations (`runWith_append`). The XOR-block result (`runWith_xorGates`) gives the first four appended values: the OR and AND of the first two inputs, the negated AND, and their XOR. Apply the same result to the second XOR block, whose inputs are the first block’s XOR output and the carry input; its index bounds follow because the first block has added four values. This supplies the next four values, including the second XOR output. The final OR gate reads the first AND output and the second carry-AND output, producing the stated carry output. The execution rules for a single gate and for the empty tail (`runWith_cons`, `runWith_nil`), together with the input index bounds, identify these last values exactly as claimed.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_xorGates`, `BoolCircuit.runWith_cons`, `BoolCircuit.runWith_nil`.
