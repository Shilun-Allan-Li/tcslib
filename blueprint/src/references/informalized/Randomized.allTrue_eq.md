<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.allTrue_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the all-true transducer

**Claim.** For every finite Boolean list $l$, the transducer that emits true on each input bit produces a list of $l.length$ copies of true.

**Proof.** Induct on $l$. For the empty list, both the transducer output and the list of zero copies are empty. For a list with head bit $b$ and tail $l$, the transducer emits the single bit true for $b$, then continues on $l$. By the induction hypothesis the tail output is $l.length$ copies of true, so concatenating the first true gives exactly $l.length+1$ copies, as required.
