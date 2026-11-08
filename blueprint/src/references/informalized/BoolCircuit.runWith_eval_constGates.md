<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.runWith_eval_constGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of constant gates

**Claim.** Evaluating the constant gates corresponding to a Boolean list appends exactly that list to the initial value list.

**Proof.** Induct on the Boolean list, allowing the initial list to vary. For the empty list, no gates are evaluated and the result is unchanged. For a first Boolean value $b$, its constant gate has no arguments and is labelled AND when $b$ is true and OR when $b$ is false; its output is therefore $b$. The execution rule (`runWith_cons`) appends this value before evaluating the gates for the tail. The induction hypothesis says those remaining gates append exactly the tail, giving the initial list followed by the whole Boolean list.

**Key facts.** `BoolCircuit.runWith_cons`.
