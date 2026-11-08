<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_verify_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Halting Verdict

**Claim.** When the verifier configuration is halted, one host-machine step halts and outputs the one-bit word that is true exactly when the verifier output is $[1]$.

**Proof.** The host machine is in its verifier phase with the verifier state component halted. Its transition therefore enters the halting branch, emits the Boolean verdict determined by whether the stored summary is true, and sets the host state to halted. The stored summary is true exactly when the verifier output is the one-bit word $[1]$ (`Complexity.capturedSummary_true`). Thus the emitted one-bit word is precisely the claimed verdict.

**Key facts.** `Complexity.capturedSummary_true`.
