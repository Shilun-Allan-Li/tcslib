<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satMax_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum-pass computation

**Claim.** For every CNF formula $\varphi$ over natural-number variables, the intercepted maximum-pass machine on its serialization halts with output consisting of $N(\varphi)$ true bits by the stated time bound.

**Proof.** By the startup lemma, there is a time $t\le 3|\mathrm{enc}(\varphi)|+5$ when the machine is in its streaming entry configuration, with counter length $N(\varphi)$, blank buffer, and empty output (Complexity.satMax_start). The variable count is at most the serialization length: decoding the serialization recovers $\varphi$ (Std.Sat.CNF.decode_serialize), and the decoded formula's variable count is bounded by its word length (Std.Sat.CNF.numVars_decode_le). From the streaming configuration, the completion lemma says that after another $N(\varphi)+1$ steps the machine halts and has output consisting of $N(\varphi)$ true bits (Complexity.satMax_finish). Splitting the run at time $t$ and concatenating these two segments gives the desired computation in $t+N(\varphi)+1$ steps. The variable-count bound and the bound on $t$ imply this is at most $4|\mathrm{enc}(\varphi)|+6$; a computation that has halted with the specified output remains a computation with that output at any later time (Turing.FinTM.ComputesInTime.mono).

**Key facts.** `Complexity.satMax_start`, `Std.Sat.CNF.decode_serialize`, `Std.Sat.CNF.numVars_decode_le`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.satMax_finish`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
