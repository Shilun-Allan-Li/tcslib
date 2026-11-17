<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonCount_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incremented Canonical Count

**Claim.** For every Boolean word $w$, incrementing the word formed by appending a zero succeeds, and the resulting canonical count has length $|w|+1$ and binary value one greater than the value of $w$.

**Proof.** Induct on $w$. For the empty word, appending false produces the one-bit zero word, and the three claims follow by evaluating the definition of increment and the binary value. For $w=b::u$, split on $b$. If $b$ is false, incrementing the appended word changes this first false bit to true and leaves the rest unchanged; the length is preserved at $|w|+1$, and the binary value increases by one because the low-order bit changes from zero to one. If $b$ is true, incrementing carries through that bit: by the induction hypothesis, incrementing $u$ followed by false succeeds, has length $|u|+1$, and adds one to the value of $u$. The result for $w$ is therefore false followed by the incremented tail. Its length is one plus the tail length, and its value is twice the tail value, which equals twice the value of $u$ plus two. The original value of $w$ is twice the value of $u$ plus one, so the result is exactly one larger.
