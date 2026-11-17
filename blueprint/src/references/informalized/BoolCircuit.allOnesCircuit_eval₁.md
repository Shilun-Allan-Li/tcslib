<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.allOnesCircuit_eval₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the All-Ones Circuit

**Claim.** For every natural number $n$ and assignment $x:\mathrm{Fin}(n)\to\mathrm{Fin}(2)$, the all-ones circuit evaluates to $\prod_{i\in\mathrm{Fin}(n)}x(i)$ in $\mathrm{Fin}(2)$.

**Proof.** The circuit has a single gate at its sole layer, and that gate is the AND operation indexed by all inputs in $\mathrm{Fin}(n)$. Its value on the assignment $x$ is therefore, by the definition of this gate, the product of the values $x(i)$ over all $i\in\mathrm{Fin}(n)$. The output is that gate’s value, giving the stated equality.
