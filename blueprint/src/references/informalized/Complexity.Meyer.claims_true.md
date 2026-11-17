<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.claims_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True claims determine the configuration

**Claim.** If the numerical valuation makes the state-and-read claims for $\sigma,\rho$ true, then $\sigma$ is the machine's actual state-and-output summary at time $t$, and $\rho$ is its tuple of read symbols at that time.

**Proof.** Expand the conjunction asserting that all claims are true. The state component says that the valuation's state atom is true; by `stA_NumVal`, this is the answer-table entry for the proposed state-and-output summary. The correctness fact `st_true` identifies that entry with the truth value of equality to the actual summary. Since the entry is true, the proposed summary equals the actual one.

The remaining components assert that the proposed input and work-tape symbols agree with the corresponding symbol queries under the valuation. By `symvA_NumVal`, these are the answer-table symbol queries at time $t$ and index zero. Apply `sv_true_none` for the input tape and `sv_true_some` for each work tape: correctness identifies those queries with the actual symbols read at the signed offset represented by sign flag false and index zero. That offset is zero, so these are precisely the actual read symbols. Equality of the input component and, pointwise, of every work-tape component gives equality of the read tuples.

**Key facts.** `Complexity.Meyer.stA_NumVal`, `Complexity.Meyer.symvA_NumVal`, `Complexity.Meyer.st_true`, `Complexity.Meyer.sv_true_none`, `Complexity.Meyer.sv_true_some`.
