<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_fT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-state transduction

**Claim.** The Boolean-word function computed by the specified finite-state transducer is polynomial-time computable.

**Proof.** The transducer has a finite state set, so the general theorem that every finite-state transduction is polynomial-time computable applies directly. Its transition function records the pending-bit status and its output function emits the prescribed bit; therefore the resulting transduction is exactly the function in the claim.

**Key facts.** `Complexity.polyTimeComputable_transduce`.
