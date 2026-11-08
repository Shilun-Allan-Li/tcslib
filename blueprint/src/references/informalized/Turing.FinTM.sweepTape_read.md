<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepTape_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading at the Zipper Frontier

**Claim.** At the frontier coordinate $z$, the tape represented by frontier $z$ and stacks $l,r$ contains the first entry of $r$, or blank if $r$ is empty.

**Proof.** At coordinate $z$, the left-of-frontier condition is false, and the index into the right stack is $z-z=0$. Thus the tape value is the zeroth entry of $r$, joined with the optional-symbol value; this is precisely the head of $r$, or blank when the list is empty.
