<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.flatMap_exec_bitsOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of bit-printing operations

**Claim.** For any register assignment $\rho$ and bit string $w$, concatenating the outputs of the bit-printing operations associated with the bits of $w$ yields exactly $w$.

**Proof.** Induct on $w$. The empty list has no associated operations, so its concatenated output is empty. For a list with first bit $b$ and tail $w$, the associated operations consist of the operation printing $b$, followed by the operations for $w$. Their outputs concatenate as $[b]$ followed by the output for $w$. By the induction hypothesis that latter output is $w$, giving $b::w$.
