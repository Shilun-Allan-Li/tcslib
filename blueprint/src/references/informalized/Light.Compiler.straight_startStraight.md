<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.straight_startStraight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straightness of initial code

**Claim.** For all natural numbers $F$ and $N$, every instruction in the initial code formed from the pool initialization and frame initialization is a constant assignment, addition, subtraction, multiplication, load, or store instruction.

**Proof.** The initial code concatenates the pool code and the frame code. The pool code contains one subtraction followed by a list of additions. The frame code contains an initial subtraction, the zeroing code consisting of subtractions, and two additions that copy the arguments into their frame locations. Thus every instruction in either part is one of the straight instruction forms, and consequently so is every instruction in the concatenation.
