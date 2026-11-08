<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clQueryFlags_compute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Runtime for Query Flags

**Claim.** The finite binary query machine halts within the stated time and outputs, in source-time order, the $N$ flags indicating whether $r_s(p)+y_1=r_s(n)+y_0$, with words interpreted as little-endian binary numerals.

**Proof.** The completeness result for the comparison machine (`Complexity.clMatch_complete`) gives a time $b$ bounded by $N(l(5W+7)+2W+5)+1$ at which it has processed all $N$ rows and reached its return state, with the output flag tape containing exactly the desired flags in order. The initial-state identification (`Complexity.clQuery_initial`) identifies its true input configuration with the prescribed query words. The preparation simulation theorem (`Complexity.clPrepared_run`) then shows that the prepared query machine reaches this return configuration after preparation and the $b$ comparison steps; this accounts for the input-reading and row-loading portion of the runtime. At that point the output machine’s hypotheses hold: it is at its designated return state, its output is empty, and the flag tape contains the word of flags. The output construction result (`Complexity.clOutput_compute`) replays that tape to produce the desired word, taking the stated linear time in its length. The return-state behavior is justified by the prepared machine’s idle-state lemma (`Complexity.clPrepared_idle`) and the comparison machine’s return transition (`Complexity.clMatch_return`). Combining these phases gives an actual runtime no greater than the claimed expression; the flags have length $N$, and elementary arithmetic absorbs the preparation and replay bounds into that expression. The computation-time monotonicity theorem (`Turing.FinTM.ComputesInTime.mono`) supplies the exact claimed time bound.

**Key facts.** `Complexity.clMatch_complete`, `Complexity.clQuery_initial`, `Complexity.clPrepared_run`, `Complexity.clOutput_compute`, `Complexity.clPrepared_idle`, `Complexity.clMatch_return`, `Turing.FinTM.ComputesInTime.mono`.
