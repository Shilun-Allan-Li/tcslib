<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStack_pop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Popping a Represented Stack

**Claim.** For any stack tail $xs$ and symbol $a$, blanking the cell at position $-(|xs|+1)$ in the tape representation of the stack with top symbol $a$ and tail $xs$ yields the tape representation of $xs$.

**Proof.** The push identity (`Turing.bridgeStack_push`) says that the representation of $a::xs$ is obtained from the representation of $xs$ by writing the embedded symbol $a$ at position $-|xs|-1$. The target position $-|a::xs|$ is exactly $-|xs|-1$. Blanking that position therefore undoes the push: updating the already updated tape there with the blank value is the same as updating the original tape there with blank. The original representation of $xs$ is already blank at this position, since the index condition for a stack entry fails there. Thus the blanking update leaves that representation unchanged, giving the claimed equality.

**Key facts.** `Turing.bridgeStack_push`.
