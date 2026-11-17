<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateTape_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Cell After the Unary State Encoding

**Claim.** The unary state tape encoding $n$ is blank at cell $n+1$.

**Proof.** The encoding is the finite buffer consisting of a marker followed by $n$ ones, so its length is $n+1$. The buffer tape returns a symbol only at positions within its buffer and returns blank beyond it. Hence cell $n+1$, the first cell after the buffer, is blank.
