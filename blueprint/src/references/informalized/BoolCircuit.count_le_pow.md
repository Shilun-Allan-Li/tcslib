<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/ShannonProbabilistic.lean :: BoolCircuit.count_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Counting fan-in-two circuits

**Claim.** If $n,S$ are natural numbers with $1\le n$, $1\le S$, and $10nS\le 2^n$, then the number of Boolean functions on $n$ inputs computed by well-formed fan-in-two directed acyclic circuits of size at most $S$ is at most $2^{n\cdot 2(S+1)}$, and $20n(S+1)\le 9\cdot2^n$.

**Proof.** First bound the circuit count in the form needed for the exponential estimate. The elementary inequality
\[(S+1)\bigl(3(S+1)^2\bigr)^S S\le \bigl(2(S+1)\bigr)^{2(S+1)}\]
follows by bounding $(S+1)S$ by $[2(S+1)]^2$ and $3(S+1)^2$ by $[2(S+1)]^2$, then combining the powers. The hypothesis $10nS\le 2^n$, together with $S\ge1$, yields $10n\le2^n$; in particular $2(S+1)\le2^n$. Thus the displayed bound is at most $(2^n)^{2(S+1)}=2^{n\,2(S+1)}$.

The counting estimate for computable circuits (BoolCircuit.card_computable_dag_le) bounds the number of functions by $(S+1)(3(S+1)^2)^S S$. Combining it with the preceding inequalities gives the claimed bound. Finally, $10nS\le2^n$ and $S\ge1$ imply $10n\le2^n$, while the same hypothesis and $n\ge1$ give $10S\le2^n$. These estimates, together with the stated hypotheses, yield $20n(S+1)\le9\cdot2^n$ by elementary arithmetic.

**Key facts.** `BoolCircuit.card_computable_dag_le`.

**Caveat.** The Lean proof establishes the second arithmetic inequality via `nlinarith`; the prose gives its claimed conclusion but does not spell out the full arithmetic derivation from the hypotheses.
