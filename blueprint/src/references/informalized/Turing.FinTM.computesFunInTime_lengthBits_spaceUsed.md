<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_lengthBits_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length with a Space Bound

**Claim.** A finite Turing machine outputs the little-endian binary representation of the input length, halts in linear time, and uses at most a constant times the size of that length plus one work-tape cells at every time.

**Proof.** Choose `f2_counterTM` and $c=5$. The theorem `f2_counter_computes` establishes the required output and halting time $5(|x|+1)$ on every input. The accompanying bound `f2_counter_space` gives, for every input and every time, space usage at most $5(\operatorname{size}(|x|)+1)$. Together these are the claimed time and space guarantees.

**Key facts.** `Turing.FinTM.f2_counter_computes`, `Turing.FinTM.f2_counter_space`.
