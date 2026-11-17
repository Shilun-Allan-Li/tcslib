<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.constZeroCircuit_eval₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-zero circuit output

**Claim.** For every natural number $n$ and input assignment $x : \mathrm{Fin}(n) \to \mathrm{Fin}(2)$, the two-layer circuit with $n$ input nodes and a single output node evaluates to $0$.

**Proof.** Unfolding the evaluation of this circuit at its unique output reduces the value to $1-1$. The first layer is an AND gate with no inputs, whose empty product is $1$; the second layer applies NOT, defined on $\mathrm{Fin}(2)$ by subtracting the input from $1$. Thus the output is $1-1=0$ in $\mathrm{Fin}(2)$, independently of the input assignment.
