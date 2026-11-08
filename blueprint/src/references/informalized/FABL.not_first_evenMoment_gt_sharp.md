<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.not_first_evenMoment_gt_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Even-Moment Benchmark

**Claim.** Under the stated second-moment normalization, the expectation of $X^{2\cdot1}$ equals the first even-moment benchmark; in particular it cannot be strictly greater than that benchmark.

**Proof.** The first-moment case of the even-moment identity (`first_evenMoment_condition_redundant`) states directly that the expectation of $X^{2\cdot1}$ equals the benchmark. A quantity equal to the benchmark cannot be strictly greater than it, which proves the claim.

**Key facts.** `FABL.first_evenMoment_condition_redundant`.

**Caveat.** The formal theorem proves equality with the benchmark, and hence rules out strict excess; the informal statement’s phrase “cannot exceed” is stronger than this formal conclusion if interpreted as an upper-bound claim.
