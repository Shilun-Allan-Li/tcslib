<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.astep_call₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Argument Oracle Call Step

**Claim.** For a unary-first oracle call on the ordered registers $r,r'$, one machine step preserves the registers and the empty answer field, and chooses the positive or negative successor according to the oracle's answer on the encoding of $1^n$ paired with the binary representations of $v(r)$ and $v(r')$.

**Proof.** Unfold the one-step transition and substitute the hypothesis identifying the call instruction. By the transition rule for calls, the register assignment and answer field are unchanged, while the control label is the positive successor precisely when the oracle accepts the virtual input. The two-argument unary-first virtual-input identity (`Complexity.LogProg.vword_unary₂`) rewrites that input as the encoding of $1^n$ paired with the two register words, in their specified order. This is exactly the asserted step.

**Key facts.** `Complexity.LogProg.vword_unary₂`.
