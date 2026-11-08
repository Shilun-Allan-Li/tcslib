<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_answer_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Boolean Answer

**Claim.** From a configuration in state $0$, the machine that emits the bit $b$ and then halts reaches a halted configuration after two steps, with output extended by $b$.

**Proof.** The machine's transition in state $0$ is exactly the first action in the one-bit emission procedure, and its transition in state $1$ is exactly the halting action. Thus its transition function agrees at every emission stage with the prescribed emitter. Apply the general emission theorem (`Turing.FinTM.emit_halts`) to the one-bit word $[b]$, the identity state sequence on the two states, and the given configuration. Since a word of length one takes two steps to emit and halt, that theorem gives both the halted state and output $c.output ++ [b]$.

**Key facts.** `Turing.FinTM.emit_halts`.
