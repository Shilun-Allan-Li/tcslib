<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.adderCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Adder Circuit

**Claim.** For every $n$ and Boolean assignment $x$ to the $n$ input bits, the adder circuit outputs the conjunction of the bitwise agreement condition for the three blocks and the condition that the final carry is false.

**Proof.** Run the gate construction through step $n/3$. Its specification gives the resulting list length, the value at the carry index, and the value at the accumulator index: these are respectively the prescribed length, the carry from adding the first two input blocks, and the bitwise agreement of the third block with their sum (`BoolCircuit.RippleCarry.adderGatesUpTo_spec`). The accumulator index lies within this list by the accumulator-index bound (`BoolCircuit.accIdx_lt`). The circuit appends two final gates: a negation of the carry and a conjunction of the accumulated agreement value with that negated carry. The carry and accumulator indices refer to the already-built list, so the appended gates do not change those values. Reading the circuit's designated output therefore yields exactly the agreement value conjoined with the negation of the final carry. The list append and indexing identities (`BoolCircuit.runWith_append`, `BoolCircuit.runWith_cons`, and `BoolCircuit.runWith_nil`) account for passing from the constructed gate lists to these output values.

**Key facts.** `BoolCircuit.RippleCarry.adderGatesUpTo_spec`, `BoolCircuit.accIdx_lt`, `BoolCircuit.runWith_append`, `BoolCircuit.runWith_cons`, `BoolCircuit.runWith_nil`.
