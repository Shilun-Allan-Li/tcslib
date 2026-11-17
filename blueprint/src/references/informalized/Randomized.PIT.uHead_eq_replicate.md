<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.uHead_eq_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Transducer Output Is Unary

**Claim.** For every bit string $w$, the head transducer output consists entirely of $1$ bits and has length equal to its own length.

**Proof.** Induct on the input string. For the empty input, the output is empty, which is the unary string of length zero. For a nonempty input, split on its first bit. The transducer either emits one $1$ or emits nothing, and then processes the remaining input. By the induction hypothesis that remaining output is a string of $1$s; adding either zero or one leading $1$ gives a string of $1$s whose length is the length of the full output.
