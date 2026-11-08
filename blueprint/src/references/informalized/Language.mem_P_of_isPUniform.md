<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PUniformP.lean :: Language.mem_P_of_isPUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# P Membership from Uniform Circuits

**Claim.** If a Boolean circuit family is polynomial-time uniform, has fan-in at most two, and recognizes a language $L$, then $L$ belongs to polynomial time.

**Proof.** The theorem `BoolCircuit.DAGCircuitFamily.IsPUniform.language_mem_P` states that the language recognized by any polynomial-time-uniform family with fan-in at most two belongs to polynomial time. Apply it to $C$ using the given uniformity and fan-in hypotheses. The resulting membership is for $C$'s recognized language, which equals $L$ by assumption; substituting this equality yields $L\in\mathrm{P}$.

**Key facts.** `BoolCircuit.DAGCircuitFamily.IsPUniform.language_mem_P`.
