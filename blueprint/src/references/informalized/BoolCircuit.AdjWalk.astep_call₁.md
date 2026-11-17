<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.astep_call₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Argument Oracle Call Step

**Claim.** For a unary-first oracle call on register $r$, one machine step preserves the registers and the empty answer field, and chooses the positive or negative successor according to the oracle's answer on the encoding of $1^n$ paired with the binary representation of $v(r)$.

**Proof.** Unfold the one-step machine transition and use the hypothesis identifying the instruction at the given label. The transition for a call leaves the register assignment and answer field unchanged, and selects the positive successor exactly when the oracle accepts the virtual input. The virtual-input calculation for a unary-first call with one argument (`Complexity.LogProg.vword_unary₁`) identifies that input with the encoding of $1^n$ paired with the register's binary word. Substituting this form yields the asserted transition.

**Key facts.** `Complexity.LogProg.vword_unary₁`.
