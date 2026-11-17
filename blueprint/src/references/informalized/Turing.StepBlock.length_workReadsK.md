<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.length_workReadsK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Work-Tape Read Patterns

**Claim.** For every natural number $k$, the list of possible read patterns on $k$ binary work tapes has length $3^k$.

**Proof.** Proceed by induction on $k$. With zero tapes, the list consists of the unique empty read pattern, so its length is $1=3^0$. For $k+1$ tapes, the construction chooses one of three possible symbols for the first tape and pairs that choice with each read pattern on the remaining $k$ tapes. Its length is therefore three times the length for $k$, which by induction is $3\cdot 3^k=3^{k+1}$.
