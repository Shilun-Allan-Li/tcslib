<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirectTM_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Liveness under redirection

**Claim.** If $M$ halts on $x$ after exactly $t$ steps with output $w$, and the last bit of $w$ is not $b$, then the machine redirected to halt on $b$ is not halted after any number $u$ of steps from its initial configuration on $x$.

**Proof.** Fix $u$ and suppose the redirected machine is halted after $u$ steps. The run correspondence lemma identifies that configuration with the redirected image of the configuration reached by $M$ after $u$ steps (`redirect_run`). By the definition of this image, its being halted forces the original machine's state at time $u$ to be halted: if that state were live, the redirected state would still be a live state carrying the original state and output register. Thus $M$ halts at time $u$. The characterization of computation in terms of a halted state and its output (`computesInTime_iff`) now shows that $M$ computes its time-$u$ output at time $u$. Output uniqueness for computations of the same machine and input (`ComputesInTime.output_unique`) identifies this output with $w$, since $M$ also computes $w$ at time $t$. Substituting this common output and the halted state into the assumed redirected halt says precisely that the last output bit is $b$. This contradicts the hypothesis that the last bit of $w$ is not $b$.

**Key facts.** `Turing.FinTM.redirect_run`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`.
