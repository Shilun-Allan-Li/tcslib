<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.tapesOf_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating one unary tape

**Claim.** Replacing tape $t$ by the unary tape of length $m$ in the family of tapes determined by $v$ yields the family determined by updating $v(t)$ to $m$.

**Proof.** Two tape families are equal if they agree at every tape index. Fix an index $i$. If $i=t$, both updates select the unary tape of length $m$. If $i\ne t$, both retain the original tape, namely the unary tape of length $v(i)$. Thus the families agree pointwise.
