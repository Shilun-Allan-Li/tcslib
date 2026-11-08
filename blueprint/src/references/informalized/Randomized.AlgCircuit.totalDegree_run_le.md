<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.totalDegree_run_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for circuit execution

**Claim.** For a list of $m$ algebraic gates on $n$ inputs, evaluated in order at the formal variables over $\mathbb{Z}$, the total degree at every position (taking out-of-range values to be zero) is at most $2^m$.

**Proof.** Proceed by induction on the gate list, using its decomposition into an initial list followed by one final gate; the induction hypothesis applies to every position in the initial run. For the empty list, every queried value is zero, so the bound holds. For the inductive step, the run on the extended list is the initial run followed by the value computed by the last gate (`Randomized.AlgCircuit.run_append_singleton`). Its length increases by one, so the new bound is twice the previous power of two. The queried position either remains in the initial run or is the newly appended value (`Randomized.AlgCircuit.getD_append_singleton`). In the first case the induction bound implies the doubled bound. In the second, consider the final gate's form. A variable has degree one, which is at most the doubled bound; the constant one has degree zero. For addition and subtraction, the degree is bounded by the maximum of the operand degrees, and each operand is bounded by the induction hypothesis. For multiplication, the degree is at most the sum of the operand degrees; each is at most $2^m$, so their sum is at most $2^{m+1}$. These cases establish the bound for every position in the extended run.

**Key facts.** `Randomized.AlgCircuit.run_append_singleton`, `Randomized.AlgCircuit.getD_append_singleton`.
