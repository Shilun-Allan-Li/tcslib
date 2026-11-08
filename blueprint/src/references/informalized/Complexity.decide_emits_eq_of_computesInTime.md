<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.decide_emits_eq_of_computesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission Characterizes a Computed Bit

**Claim.** If $M$ halts within $t$ steps on input $x$ with output the single bit $b$, then the Boolean decision that some time $s<t$ has a snapshot whose selected transition emits $1$ equals $b$.

**Proof.** The computation hypothesis implies that the run at time $t$ has halted and its output is $[b]$ (`computesInTime_iff`). The output accumulated by time $t$ is the concatenation, over transition times $s<t$, of the optional symbols emitted from the corresponding snapshots (`output_runFrom_eq_flatMap`). Thus some such transition emits $1$ exactly when $1$ occurs in $[b]$, which is equivalent to $b=	ext{true}$. Deciding this existential proposition therefore returns the Boolean $b$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.output_runFrom_eq_flatMap`.
