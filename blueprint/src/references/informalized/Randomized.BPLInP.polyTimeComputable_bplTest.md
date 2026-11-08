<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.polyTimeComputable_bplTest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time BPL Test

**Claim.** For every finite nondeterministic Turing machine $N$ over bits and natural numbers $c,B,e$, the function sending a bit string $x$ to the one-bit output containing the value of the test on $x$ is polynomial-time computable.

**Proof.** The dynamic-programming run on input $x$ is polynomial-time computable by the stated result for `dpRun` (Randomized.BPLInP.polyTimeComputable_dpRun). The test is obtained from that run by the post-processing covered by the result for a test from a computable run (Randomized.BPLInP.polyTimeComputable_bplTest_of_run). Applying that result to the polynomial-time run proves the claim.

**Key facts.** `Randomized.BPLInP.polyTimeComputable_bplTest_of_run`, `Randomized.BPLInP.polyTimeComputable_dpRun`.
