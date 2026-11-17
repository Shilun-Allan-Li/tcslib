<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.straight_frameInit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straightness of frame initialization

**Claim.** For every natural number $n$ and every natural number $F'$, each instruction in the frame-initialization code of size $F'$ for $n$ is straight.

**Proof.** We argue by induction on $F'$. When $F'=0$, the range being traversed is empty, so the frame-initialization list has no instructions and the claim is vacuous. For the successor case, the frame initialization splits as the initialization of size $F'$ followed by two instructions: a subtraction and a store. By the induction hypothesis, all instructions in the earlier portion are straight. The two appended instructions are straight by the definition of straightness, regardless of the conditional address used in the store. Hence every instruction in the whole list is straight, using the decomposition of the successor initialization (`frameInit_succ`).

**Key facts.** `Light.Compiler.frameInit_succ`.
