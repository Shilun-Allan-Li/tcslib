<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.ComputesFunInTimeAndSpace.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of function-computation bounds

**Claim.** If a multi-tape Turing machine computes a function within input-indexed time and space bounds $t,s$, and these bounds are pointwise at most $t',s'$, then the same machine and encodings compute the function within $t',s'$.

**Proof.** Fix an input $a$. The assumed computation property provides witnesses $u\le t(a)$ and $v\le s(a)$ together with a computation using time $u$ and space $v$. By transitivity of the natural-number order and the pointwise hypotheses, $u\le t'(a)$ and $v\le s'(a)$. The same witnesses and computation therefore establish the property at input $a$ for the larger bounds. Since $a$ was arbitrary, the machine computes the function within $t',s'$.
