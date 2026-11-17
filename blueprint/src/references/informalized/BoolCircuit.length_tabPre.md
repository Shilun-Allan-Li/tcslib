<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.length_tabPre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the table prefix

**Claim.** The table prefix formed from two constant gates, one constant gate for each entry of $z$, and $W$ additional false constant gates has length $2+|z|+W$.

**Proof.** The prefix concatenates a list of two constant gates, the list obtained by mapping one constant gate over $z$, and a replicated list of $W$ constant gates. Their lengths are respectively $2$, $|z|$, and $W$, so the total is $2+|z|+W$.
