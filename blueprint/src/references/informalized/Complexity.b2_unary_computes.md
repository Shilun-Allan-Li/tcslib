<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer of Unary Computation

**Claim.** If $M$ computes $v$ within $t$ steps on the all-ones word of length $|x|$, then its input-normalized machine computes $v$ within the same time on $x$.

**Proof.** Reinterpret the normalized machine's initial configuration on $x$ as a configuration on the all-ones word of length $|x|$; the initial-configuration identity (`Complexity.b2_unary_initial`) says this is exactly $M$'s initial configuration there. The run correspondence (`Complexity.b2_unary_run`) then identifies the normalized machine's configuration after $t$ steps, under the same reinterpretation, with $M$'s configuration after $t$ steps. The hypothesis, expressed through the characterization of computation in terms of the final halted state and output (`Turing.FinTM.computesInTime_iff`), gives that this latter configuration is halted and has output $v$. Since reinterpretation preserves state and output, the normalized run has those same properties; applying the characterization again yields the claimed computation time.

**Key facts.** `Complexity.b2_unary_run`, `Complexity.b2_unary_initial`, `Turing.FinTM.computesInTime_iff`.
