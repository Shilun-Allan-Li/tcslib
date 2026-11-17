<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Packed_install -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Packed-Record Producer Installation

**Claim.** For every finite Boolean-alphabet machine and the given parameters, there is a machine that, from a suitable initial work-tape word, produces the packed records in polynomial time, halting for the first time at a positive step and with empty output.

**Proof.** The packed-record construction is polynomial-time computable with a polynomial running-time bound (`clPackedRecords_machine`). Apply the installation theorem for polynomial-time computable functions (`clA5Clean_install`) to this function. It supplies a machine and a polynomial time bound with at least one work tape, such that for every input and argument word the machine starts from the prescribed encoding of that argument, avoids halting at all earlier steps, and halts at a positive bounded time in the canonical configuration containing the function's value. Since the installed function is the packed-record function, and its emitted output is empty, this is the required behavior.

**Key facts.** `Complexity.clPackedRecords_machine`, `Complexity.clA5Clean_install`.
