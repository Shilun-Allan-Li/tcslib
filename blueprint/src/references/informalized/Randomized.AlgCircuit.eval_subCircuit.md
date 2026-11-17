<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.eval_subCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a circuit difference

**Claim.** Let $C$ and $C'$ be algebraic circuits on the same finite set of inputs, each with at least one gate, and let the inputs take values in a commutative ring. The circuit formed by adjoining the shifted gates of $C'$ to those of $C$ and then subtracting their output nodes evaluates to the value of $C$ minus the value of $C'$.

**Proof.** Because both gate lists are nonempty, their lengths are positive, so their output indices are their lengths minus one. Appending the gates of $C'$ with indices shifted by the length of $C$ makes the combined run produce the two runs consecutively (`run_append_shift`). Each run has as many values as its gate list (`length_run`), so the output indices in the combined list point to the respective circuit outputs. The final subtraction gate is evaluated after those two runs; appending a single gate appends its evaluation to the run (`run_append_singleton`). Its operands therefore read the outputs of $C$ and $C'$, respectively, and the result is $C(x)-C'(x)$.

**Key facts.** `Randomized.AlgCircuit.length_run`, `Randomized.AlgCircuit.run_append_shift`, `Randomized.AlgCircuit.run_append_singleton`.
