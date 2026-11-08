<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.runWith_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Gate Relabeling

**Claim.** If relabeling a gate by $h$ does not change its output on any list of previous outputs, then applying $h$ to every gate in a list does not change the result of evaluating that list.

**Proof.** Induct on the gate list, allowing the initial output list to vary. The empty list leaves the initial list unchanged on both sides. For a list beginning with $g$ and followed by a tail, evaluation first appends the output of $g$ and then evaluates the tail (`runWith_cons`). On the relabeled side, the first gate is $h(g)$; the hypothesis on $f$ makes its appended output equal to that of $g$. The induction hypothesis applied to the tail with this common updated list gives equal final outputs.

**Key facts.** `BoolCircuit.runWith_cons`.
