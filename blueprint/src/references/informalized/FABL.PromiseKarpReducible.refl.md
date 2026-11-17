<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/Complexity.lean :: FABL.PromiseKarpReducible.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of promise reductions

**Claim.** Every binary promise problem reduces to itself by a polynomial-time map preserving its promised yes- and no-instances.

**Proof.** Take the identity map on binary strings. It is polynomial-time, and it sends every promised yes-instance to itself and every promised no-instance to itself. Hence it preserves both promised classes and witnesses the reduction.
