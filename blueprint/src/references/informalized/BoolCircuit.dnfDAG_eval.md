<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.dnfDAG_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the DNF Circuit

**Claim.** For every natural number $n$, Boolean function $f$ on assignments to $n$ variables, and assignment $x$, the DNF circuit constructed from the satisfying assignments of $f$ evaluates at $x$ to $f(x)$.

**Proof.** The DNF construction specification (BoolCircuit.dnf_spec) identifies the output value with the value of an OR gate on the vertices produced by the conjunction trees, evaluated after the initial negation gates. The specification for those minterm trees (BoolCircuit.minterms_spec) identifies each such vertex with the corresponding conjunction of minterm leaves. Thus the output is the disjunction, over the satisfying assignments $v$ in the enumerated list, of the minterm value at $x$. The minterm evaluation theorem (BoolCircuit.mintermLeaves_eval) says that this value is true exactly when $x=v$. Consequently the disjunction is true exactly when $x$ occurs in the satisfying-assignment list. That list is the filtered set of assignments where $f(v)=	ext{true}$, so this condition is equivalent to $f(x)=	ext{true}$. Since both sides are Boolean values, they are equal.

**Key facts.** `BoolCircuit.dnf_spec`, `BoolCircuit.minterms_spec`, `BoolCircuit.mintermLeaves_eval`.
