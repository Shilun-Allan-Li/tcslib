<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.minterm_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of a minterm

**Claim.** For any nonnegative integer $n$ and Boolean assignment $v$ on $n$ variables, the minterm specified by $v$ has size $n+1$.

**Proof.** The minterm is an AND node whose children are the literals indexed by the elements of `Fin n`. Each child is a literal and has size $1$. The fold-size formula says that mapping a list of length $n$ to objects of size $1$ gives total child size $n$ (`foldr_size_map`). The AND node itself contributes one more, so the minterm has size $1+n=n+1$.

**Key facts.** `BoolCircuit.foldr_size_map`.
