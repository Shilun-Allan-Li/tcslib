<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.bitsToNat_digits_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Boolean digit values

**Claim.** For every finite Boolean list $w$, each entry of the list obtained by replacing false by $0$ and true by $1$, then appending $1$, is less than $2$.

**Proof.** Take an entry of the appended list. If it comes from the mapped Boolean list, it is either $0$ or $1$, according as that Boolean is false or true, and both are less than $2$. If it comes from the appended singleton, it is $1$, also less than $2$.
