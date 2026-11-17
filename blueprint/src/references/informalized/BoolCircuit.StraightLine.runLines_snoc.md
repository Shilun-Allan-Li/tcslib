<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.runLines_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After One Appended Statement

**Claim.** Evaluating the list $ss$ followed by $s$ gives the evaluation of $ss$ with the value of $s$ on that evaluation appended.

**Proof.** The execution of a concatenated list is obtained by first folding over its initial segment and then folding over the appended segment. Here that segment is the singleton list containing $s$, so the fold appends exactly the one value $s$ evaluates to, using the values already produced by $ss$.
