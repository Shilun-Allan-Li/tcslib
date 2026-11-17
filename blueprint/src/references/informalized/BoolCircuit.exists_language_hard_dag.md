<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.exists_language_hard_dag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A language hard for bounded-size DAG circuits

**Claim.** There is a language over Boolean strings such that any size bound that is at most $2^n/(10n)$ at some length $n>1$ is insufficient for a fan-in-two acyclic circuit family to recognize the language.

**Proof.** For each length $m>1$, choose a Boolean function $F_m$ that disagrees somewhere with every well-formed fan-in-two acyclic circuit of size at most $2^m/(10m)$, using the hard-function theorem (`exists_hard_function_dag`). For lengths $m\le1$, set $F_m$ to the constant false function. Define the language to contain exactly those strings $w$ for which $F_{|w|}(w)$ is true. Suppose a fan-in-two circuit family of size at most $T(m)$ recognizes this language, and choose a length $n>1$ with $T(n)\le2^n/(10n)$. Recognition implies that at length $n$ its circuit agrees with $F_n$ on every Boolean input: each input vector corresponds to a string of length $n$ via its list of bits, and equality of the recognized languages gives equality of their Boolean acceptance values. But the circuit has size at most $T(n)$, hence at most $2^n/(10n)$, so the hard-function property gives an input where it disagrees with $F_n$. This contradiction rules out the proposed family.

**Key facts.** `BoolCircuit.exists_hard_function_dag`.
