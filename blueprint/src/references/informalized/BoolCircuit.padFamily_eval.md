<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.padFamily_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Padded Circuit Family

**Claim.** For every input length $n$ and every assignment $x$ to its $n$ inputs, the padded circuit for $F_n$ evaluates to $F_n$ on the restriction of $x$ to its first $\ell(n)$ inputs.

**Proof.** By definition, the padded circuit is obtained by widening the universal circuit for $F_n$ from $\ell(n)$ inputs to $n$ inputs. Widening preserves evaluation by evaluating the original circuit on the assignment $i\mapsto x(\mathrm{Fin.castLE}(i))$ (the widening evaluation theorem, `BoolCircuit.widenCircuit_eval`). The universal circuit computes the function used to define it, so this evaluation is $F_n$ of that restricted assignment (`BoolCircuit.universalCircuit_eval`). This restricted assignment is precisely the meaning of $\mathrm{onFirst}$, giving the stated equality.

**Key facts.** `BoolCircuit.widenCircuit_eval`, `BoolCircuit.universalCircuit_eval`.
