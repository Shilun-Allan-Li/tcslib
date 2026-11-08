<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterSplit_of_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Split Solver from a Round Contract

**Claim.** Under the stated start and round contracts, there is a finite-state Boolean Turing machine that outputs the encoding of the split at the least index $i\le |w|$ satisfying $i+f(i)=|w|$, or the empty word if there is no such index, and halts after exactly $c(|w|+1)(T_E(|w|+1)+|w|+2)$ steps for some natural number $c$.

**Proof.** First choose a machine that computes the binary bits of the input length in time linear in that length. Combining its running-time constant with the contract constant $A$, and using $|w|+1\le T_E(|w|+1)+|w|+2$, we obtain a machine that computes the bits needed by the loop search within a bound proportional to $A+ a$ times $T_E(|w|+1)+|w|+2$, where $a$ is the length-computation constant. The loop-search theorem then applies to the body machine: the invariant holds initially for the empty candidate and is preserved by the split step; the start contract reaches the anchor configuration with blank work tapes, and the round contract supplies each positive-length round, either halting with the required encoded split or returning to the anchor with the updated candidate. It yields a machine whose search result is the first accepted iterate of the split step, with a time bound proportional to $(n+2)(A+a)(T_E(n+1)+n+2)$, where $n=|w|$. The search-output identity identifies that output with the least-index split specified in the claim. Finally, the elementary loop bound absorbs the factor $n+2$ into $2(n+1)$ and adjusts the constant, giving the claimed time form. The resulting computation time is exact: the machine's time guarantee is extended to the stated bound using the monotonicity of computations in time.

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.FinTM.exists_loopFindTM`, `Turing.FinTM.splitStep_inv`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.emitterSplit_loop_bound`, `Turing.FinTM.emitterSplit_result`.

**Caveat.** The supplied upstream statement for exists_loopFindTM is truncated, so its complete hypotheses and conclusion are not available here; the account follows its application as shown in the proof source.
