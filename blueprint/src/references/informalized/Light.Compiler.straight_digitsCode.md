<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.straight_digitsCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straight instructions in digit code

**Claim.** For every integer location $c$ and finite list of natural-number digits, each instruction in the code generated from those digits at location $c$ is straight.

**Proof.** Induct on the digit list. For the empty list, the generated code consists of one subtraction instruction, which is straight. For a list with head digit $d$ and tail $L$, the code consists of the code for $L$, followed by an addition instruction, and followed by one more addition instruction exactly when $d\ne0$. By induction, all instructions in the tail code are straight; the newly appended instructions are additions and hence straight. This covers both cases $d=0$ and $d\ne0$.
