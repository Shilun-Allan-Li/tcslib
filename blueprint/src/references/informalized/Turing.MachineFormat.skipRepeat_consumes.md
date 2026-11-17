<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.skipRepeat_consumes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated skipper consumption bound

**Claim.** If every successful application of a partial reader consumes at least $b$ bits, then a successful sequence of $m$ applications consumes at least $bm$ bits, leaving a suffix whose length satisfies $bm+|y|\le |x|$.

**Proof.** Induct on the number $m$ of applications. For zero applications, success means the final suffix is the original string, so the inequality is immediate. For $m+1$, successful repeated reading decomposes into a first successful read from $x$ to some intermediate suffix $z$, followed by $m$ successful reads from $z$ to $y$. The one-read hypothesis gives $b+|z|\le |x|$, and the induction hypothesis gives $bm+|y|\le |z|$. Adding these inequalities yields $b(m+1)+|y|\le |x|$.
