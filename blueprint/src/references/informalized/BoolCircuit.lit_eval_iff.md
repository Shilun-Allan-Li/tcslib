<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.lit_eval_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Boolean literal

**Claim.** The literal at index $i$ with polarity $b$ evaluates to true under assignment $x$ exactly when $x(i)=b$.

**Proof.** Split on the polarity. If $b$ is true, the literal evaluates to $x(i)$, so it is true exactly when $x(i)=\mathrm{true}$. If $b$ is false, it evaluates to the negation of $x(i)$, which is true exactly when $x(i)=\mathrm{false}$. These are precisely the two cases of $x(i)=b$.
