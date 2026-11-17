<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.SLOperand.lit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a literal operand

**Claim.** The literal operand specified by $l=(k,b)$ evaluates to true exactly when $x(k)=b$.

**Proof.** Write $l=(k,b)$ and split into the two possible Boolean values of $b$ and the two possible values of $x(k)$. If $b$ is true, the literal operand is $x_k$, so its evaluation is true exactly when $x(k)$ is true. If $b$ is false, it is $\neg x_k$, which is true exactly when $x(k)$ is false. These four cases give the Boolean equality test $x(k)=b$.
