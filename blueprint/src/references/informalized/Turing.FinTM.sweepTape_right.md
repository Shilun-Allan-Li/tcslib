<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweepTape_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing and Moving Right on the Zipper

**Claim.** Updating the tape represented by frontier $z$, left stack $l$, and right stack $a::r$ at position $z$ to value $b$ gives the same tape function as frontier $z+1$, left stack $b::l$, and right stack $r$.

**Proof.** Compare the tape functions at an arbitrary coordinate $p$. If $p=z$, the update sets the value to $b$, and the new representation reads the first entry of its left stack, also $b$. If $p\ne z$, the update has no effect. For $p<z$, both representations read from the left stack, with the new representation's index increased by one to account for the newly placed frontier cell $b$. For $p>z$, both read from the right stack, again with the new representation's index increased by one because its frontier has shifted right. The corresponding entries agree after removing the added first element in each stack.
