<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Compare_compute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Binary Sum Comparison

**Claim.** Given four binary words, the comparator halts within $35(|arg|+1)$ steps on their encoded fields and outputs the one-bit truth value of whether the sums of the first two and last two little-endian values agree.

**Proof.** Encode the four words as fields and let $arg$ be the resulting input. Each field has length at most $|arg|$ (`Complexity.clFields_width`), so their maximum length is also at most $|arg|$. The prepared-machine simulation lemma (`Complexity.clPrepared_run`) runs the comparator on these fields and places its resulting configuration into the prepared machine, with setup cost bounded by $2|arg|+4+4(3|arg|+7)$. The comparator's run lemma (`Complexity.clCmp_run`) says that after $2$ times the maximum field length plus $2$ further steps, its control state records the verdict. The first-arrival lemma (`Complexity.clFirst`) selects a positive time $t$ at which the prepared machine first reaches the verdict state. Those verdict states are idle (`Complexity.clPrepared_idle`), so the state cannot have been reached earlier and then left; this first-arrival property also ensures the run stays away from verdict states before $t$. Up to that time, the prepared machine agrees with the comparator machine on all states outside the verdict states. The state-agreement simulation theorem (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`) therefore transfers the run back to the comparator. One more step emits the verdict bit and halts. Its value is the claimed equality test by the verdict characterization (`Complexity.clCmpVerdict_spec`). Combining the setup, comparison, and final step bounds gives $t+1\le 35(|arg|+1)$, and the computation-time monotonicity principle (`Turing.FinTM.ComputesInTime.mono`) allows the stated time bound.

**Key facts.** `Complexity.clFields_width`, `Complexity.clPrepared_run`, `Complexity.clCmp_run`, `Complexity.clPrepared_idle`, `Complexity.clFirst`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Complexity.clCmpVerdict_spec`, `Turing.FinTM.ComputesInTime.mono`.
