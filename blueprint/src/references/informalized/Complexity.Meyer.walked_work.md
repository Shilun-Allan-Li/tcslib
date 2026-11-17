<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.walked_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Symbol After Repeated Walks

**Claim.** After $a$ repetitions of the simulated walk on work tape $h$, the scanned symbol is the original tape content at the original head position shifted by $-a$ when $neg$ is true and by $a$ otherwise.

**Proof.** The iterate formula for a work-tape walk (`wstep_some_iterate`) says that the tape contents remain unchanged and the head on tape $h$ moves by the signed displacement $\operatorname{sgnZ}(neg,a)$. Reading the work-tape symbol means evaluating the original tape content at the current head position. Substituting the displaced position therefore gives exactly the original tape content at the original head position plus that signed displacement, which is the claimed value of $RW$.

**Key facts.** `Complexity.Meyer.wstep_some_iterate`.
