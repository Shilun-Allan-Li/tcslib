<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.length_startStraight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straight Start Code Length

**Claim.** For all natural numbers $F$ and $N$, the straight start code formed from the pool code and frame code has length $N+F+4$.

**Proof.** The pool code has one initial instruction and one instruction for each of the $N$ indices in the range, so its length is $N+1$. The frame code has one initial instruction, one zeroing instruction for each of the $F$ indices, and two final argument-copy instructions, so its length is $F+3$. Since the straight start code concatenates these lists, its length is $(N+1)+(F+3)=N+F+4$.
