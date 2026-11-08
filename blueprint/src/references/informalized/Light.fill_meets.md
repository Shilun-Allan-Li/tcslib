<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Copy.lean :: Light.fill_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the fill procedure

**Claim.** Under the word-bound and destination-space assumptions, the specified fill procedure has an execution within the stated time bound whose final memory contains $n$ copies of $x$ beginning at $dst$ and agrees with the initial memory outside that segment.

**Proof.** The fill procedure is the pass whose counter starts at zero, runs for $n$ iterations, and stores $x$ at the destination offset by the current counter. Apply the pass-execution result (`Light.Ends.pass`) with the stored value at each iteration equal to $x$. Its iteration hypotheses hold because the value expression is safe and evaluates to $x$; the completed pass yields the memory obtained by writing $x$ at each of the $n$ positions, with the counter at $n$. The space bound and destination assumption supply the pass theorem's safety conditions, and its time estimate gives the required bound after substituting the value expression's cost. The segment of the resulting memory is the list of $n$ copies of $x$ by the write-segment fact (`Light.seg_wrote`) and the characterization of entries in a replicate list. The pass theorem also supplies agreement with the original memory outside the written positions. Finally, the procedure body is the designated fill body, so the body execution gives the claimed procedure execution by `Light.Meets.of_body`.

**Key facts.** `Light.Ends.pass`, `Light.seg_wrote`, `Light.Meets.of_body`.
