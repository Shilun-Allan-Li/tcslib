<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.universalCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Universal Circuit

**Claim.** For a Boolean function $f$ on assignments to $n$ variables and any assignment $x$, the universal circuit for $f$ evaluates to $f(x)$.

**Proof.** The universal circuit is an OR of the minterms for assignments $v$ with $f(v)=1$. An OR node evaluates to true exactly when at least one child does (`TreeCircuit.eval_node_false_iff`). A minterm indexed by $v$ evaluates to true exactly on the assignment $v$ (`minterm_eval_iff`). Thus, if the circuit evaluates to true at $x$, some included minterm is true there, so its index is $x$ and $f(x)=1$. Conversely, if $f(x)=1$, then $x$ is among the assignments used to construct the circuit, and its minterm evaluates to true at $x$. Therefore the circuit evaluates to true exactly when $f(x)=1$, which proves equality of the Boolean values.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_false_iff`, `BoolCircuit.minterm_eval_iff`.
