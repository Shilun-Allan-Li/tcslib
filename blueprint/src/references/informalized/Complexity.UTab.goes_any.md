<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.goes_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Simulation of a Boolean Turing Machine

**Claim.** For a finite-state Boolean Turing machine and a finite Boolean word $w$, there are a final register assignment, input position, output word, and step bound $B\le 60(k+1)(L+30)(|w|+1)^3$ such that the counter program, started at its initial label with zero registers and input position, reaches a halted state with those results, appending the chosen output to any initial output in at most $B$ steps.

**Proof.** First establish a uniform estimate: for every $L\ge 0$, $3L+10\le \mathrm{emitC}(M)(L+1)^3$. Indeed, the definition of $\mathrm{emitC}$ gives $60\le\mathrm{emitC}(M)$, while $L+1\le(L+1)^3$; these inequalities imply the estimate. Now classify the input word using `classify` into the following cases.

1. If $w$ consists entirely of $a$ ones, the program reads those ones at its initial label, incrementing the input-count register and consuming $a$ symbols (`goes_rN`). It then reads the end of the word (`goes_rd_end`) and halts (`goes_stop`). Concatenating these simulations gives the required final configuration and output, and the uniform estimate bounds the steps by the stated cubic expression.

2. Otherwise write $w$ as $1^a0r$, and classify the remainder $r$. If $r=1^b$, the program first reads the initial $a$ ones, consumes the zero, and prints that zero. It then reads the next $b$ ones while counting them in the time register, detects the end of input, and halts. These stages are supplied respectively by `goes_rN`, `goes_rd_false`, `goes_out`, `goes_rT`, `goes_rd_end`, and `goes_stop`; their simulations compose by concatenation. The same uniform estimate, with the input length expressed as $a+1+b$, gives the required bound.

3. If $r=1^b0z$, split again according to whether $b=0$. When $b=0$, `goes_prefix` simulates the input prefix and reaches the layout label; since the time register is zero, one zero-register branch takes the program directly to its stop label (`goes_jz_zero`), after which `goes_stop` halts it. The run-bound estimate for this case is at most the claimed cubic bound because $a+|z|+3$ is bounded by $|w|+1$.

4. When $b>0$, `goes_emit` supplies a simulation that produces the encoded computation table and a run bound. Its bound is at most $\mathrm{emitC}(M)(a+b+|z|+3)^3$ by `runBound_le`. The quantity $a+b+|z|+3$ is at most $|w|+1$, so monotonicity of cubing gives the desired bound. In each case, `Goes` allows any initial output word, and composition appends the successive output segments, yielding the asserted append-only behavior.

**Key facts.** `Complexity.UTab.classify`, `Complexity.UTab.goes_rN`, `Complexity.CounterProg.goes_rd_end`, `Complexity.UTab.goes_stop`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_out`, `Complexity.UTab.goes_rT`, `Complexity.UTab.goes_prefix`, `Complexity.CounterProg.goes_jz_zero`, `Complexity.UTab.goes_emit`, `Complexity.UTab.runBound_le`.
