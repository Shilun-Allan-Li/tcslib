<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecordOutput_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Recorder Time

**Claim.** The output machine computes the recorded counter rows through time $T$ in at most the stated quadratic bound in the input length.

**Proof.** Let $x$ be the packed input and let each initial recorder tape word be one of the fields packed into $x$. Every such field has length at most $|x|$, by the width bound for a packed field (`clFields_width`); thus the hypothesis of the recorder-output time bound holds with $W=|x|$. The designated clock tape contains a unary word of length $T$, so the same bound gives $T\le |x|$. Apply the recorder trajectory output result (`clRecordOutput_compute`) with this width bound. Its time is at most $2|x|+8+((k'+4)(3|x|+7)+(8F+7)(T+1)^2)$. Using $T\le |x|$, the size estimate (`clRecord_size_budget`) bounds this expression by $(10+10(k'+4)+(8F+7))(|x|+1)^2$. The machine also computes at every larger time, by time monotonicity (`ComputesInTime.mono`), proving the asserted at-most bound.

**Key facts.** `Complexity.clFields_width`, `Complexity.clRecordOutput_compute`, `Complexity.clRecord_size_budget`, `Turing.FinTM.ComputesInTime.mono`.
