<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.Goes.congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Changing run endpoints

**Claim.** A bounded-run property remains valid when the initial and final register assignments, input positions, output suffix, and step bound are replaced by equal values or a larger bound, as in the hypotheses.

**Proof.** The equalities identify the proposed initial and final register assignments, input positions, and output suffix with those in the given run property. Substituting these equal quantities reduces the goal to the same endpoints and output suffix. The original property supplies, for each output word, a run of some length at most $b$; since $b\le b'$, that same run has length at most $b'$. This is the monotonicity of the run bound (`Complexity.CounterProg.Goes.mono`).

**Key facts.** `Complexity.CounterProg.Goes.mono`.
