<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup Copy Configuration

**Claim.** For every Boolean word $x$ and every $i\le |x|$, after $i$ steps the countdown emitter started on $x$ is in its copy phase, with input head at $i+1$, the first $i$ bits of $x$ on its work tape, work head at $i$, and empty output.

**Proof.** Induct on $i$. At $i=0$, the initial configuration has its input head at position one, blank work tape with head at zero, and empty output, which is exactly the asserted configuration with the empty prefix copied. For the successor step, the induction hypothesis gives the copy-phase configuration after $i$ steps. Since $i<|x|$, the one-step copy rule reads the next input bit, writes it at the current work-head position, and advances both heads by one while keeping the output empty. This is precisely the claimed configuration after $i+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.a2_copy_step`.
