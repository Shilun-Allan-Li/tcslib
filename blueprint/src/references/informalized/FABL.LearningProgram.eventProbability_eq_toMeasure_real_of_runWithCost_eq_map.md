<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.eventProbability_eq_toMeasure_real_of_runWithCost_eq_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Event probability under a mapped law

**Claim.** If running the program has the same output-and-cost law as sampling $x$ from $\mu$ and returning $(f(x),c)$, then for every predicate $E$ on outputs, the program’s event probability equals the measure under $\mu$ of the inputs whose image under $f$ satisfies $E$.

**Proof.** Replace the law of the program’s outcome by the assumed mapped law. The event that the mapped outcome’s output satisfies $E$ has as its preimage exactly the set of inputs $x$ for which $E(f(x))$ holds; the fixed cost coordinate does not affect membership in this event. The outer measure of a mapped measure on this event is therefore the measure of that preimage. Since a probability mass function’s measure and outer measure agree on measurable sets, this outer measure equals the measure of $\{x\mid E(f(x))\}$. Taking real values preserves the equality, yielding the claimed formula.
