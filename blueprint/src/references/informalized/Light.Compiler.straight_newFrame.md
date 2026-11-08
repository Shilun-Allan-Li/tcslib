<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.straight_newFrame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straightness of new-frame code

**Claim.** For all natural numbers $F,n,$ and $r$, every instruction in the code that creates a new frame of size $F$ for $n$ arguments with return index $r$ is straight.

**Proof.** The new-frame code is a concatenation of three parts: an initial subtraction, the frame initialization of size $F$, and a final block consisting of an addition, a store, and another addition. The initial and final instructions are all straight by their instruction forms. Every instruction in the middle part is straight by the frame-initialization result (`straight_frameInit`). Therefore every instruction in the concatenated code is straight.

**Key facts.** `Light.Compiler.straight_frameInit`.
