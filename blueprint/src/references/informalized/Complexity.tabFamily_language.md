<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableau.lean :: Complexity.tabFamily_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language of the Tableau Family

**Claim.** If $M$ decides $L$ within time $C(n+1)^d$, then the tableau circuit family with time bound $(C+1)(n+1)^d$ accepts exactly $L$.

**Proof.** Fix an input word $w$. By the characterization of circuit-family language membership (`BoolCircuit.DAGCircuitFamily.mem_language_iff`), it suffices to identify whether the circuit at length $|w|$ evaluates to true. The tableau circuit evaluation theorem (`Complexity.cfgTab_eval`), applied with empty auxiliary input, says its value is the Boolean decision that $M$ emits $1$ at some time strictly before $(C+1)(|w|+1)^d$. The assumed decision bound gives the same output within $C(|w|+1)^d$ steps. Since $C\le C+1$, monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) extends this computation to the larger tableau bound. The theorem identifying emissions with the computed output (`Complexity.decide_emits_eq_of_computesInTime`) therefore makes the circuit value equal to the indicator of membership of $w$ in $L$. Unfolding that indicator gives the desired equivalence for every $w$, hence equality of the two languages.

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_iff`, `Complexity.cfgTab_eval`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.decide_emits_eq_of_computesInTime`.
