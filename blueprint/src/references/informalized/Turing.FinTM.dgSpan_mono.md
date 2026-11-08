<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgSpan_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Span Bounds

**Claim.** Widening the interval containing all work-head positions preserves the endpoint of the run and gives the same run with the wider bounds.

**Proof.** The endpoint equation is unchanged. At every time $u\le t$, the original lower bound gives $\mathrm{lo}\le$ the head position, and $\mathrm{lo}'\le\mathrm{lo}$ therefore gives the new lower bound. Likewise, the head position is at most $\mathrm{hi}\le\mathrm{hi}'$, giving the new upper bound.
