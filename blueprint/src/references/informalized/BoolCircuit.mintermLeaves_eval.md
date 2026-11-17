<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.mintermLeaves_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of Minterm Leaves

**Claim.** For assignments $v,x : \mathrm{Fin}(n) \to \{\mathrm{false},\mathrm{true}\}$, the AND gate on the minterm leaves specified by $v$, evaluated after the input-negation gates have been run on $x$, equals the indicator of the equality $x=v$.

**Proof.** An AND gate evaluates to true exactly when every one of its input leaves evaluates to true. The leaves are indexed by the variables $i$, and the value at the leaf selected by $v(i)$ after the input-negation gates have run is $x(i)$ if $v(i)$ is true and the negation of $x(i)$ otherwise. In either case this value is true exactly when $x(i)=v(i)$ (`vertexValue_litVertex`). Thus all leaves evaluate to true exactly when the two assignments agree at every index, which is equivalent to $x=v$. The Boolean value of the gate is therefore true exactly when $x=v$, as asserted.

**Key facts.** `BoolCircuit.vertexValue_litVertex`.
