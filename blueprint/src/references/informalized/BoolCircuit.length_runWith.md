<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.length_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length after gate evaluation

**Claim.** For any gate-evaluation function $f$, finite gate list $gs$, and initial value list $init$, running the gates in sequence produces a list of length $|init|+|gs|$.

**Proof.** Induct on the gate list, allowing the initial list to vary. With no gates, evaluation returns the initial list, so the claim holds. For a list beginning with gate $g$, the recursion for `runWith` evaluates $g$ first and then runs the remaining gates with the extended initial list $init$ followed by the single value $f(g,init)$. By the induction hypothesis, the resulting length is $(|init|+1)+|gs|$, which equals $|init|+|g::gs|$.

**Key facts.** `BoolCircuit.runWith_cons`.
