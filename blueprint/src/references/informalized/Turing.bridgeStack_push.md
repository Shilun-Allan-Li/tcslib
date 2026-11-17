<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStack_push -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pushing onto a Represented Stack

**Claim.** For any stack $xs$ and symbol $a$, writing the embedded symbol $a$ at position $-|xs|-1$ in the tape representation of $xs$ yields the tape representation of the stack with $a$ prepended to $xs$.

**Proof.** Compare the two tape functions at an arbitrary integer position $z$. If $z=-|xs|-1$, the update writes the embedded symbol $a$ there, and this is exactly the first cell assigned to the prepended symbol in the representation of $a::xs$. Otherwise the update does not affect the value at $z$. If $z+|xs|$ is nonnegative, then $z+|a::xs|=z+|xs|+1$ is also nonnegative, and the list index for $a::xs$ is one larger than the index for $xs$. The lookup in the cons list at that shifted index returns the same tail entry as the original lookup. If $z+|xs|$ is negative, then, since $z$ is not the newly written position, $z+|a::xs|$ is negative as well; both representations are blank there. The tape functions therefore agree at every cell.
