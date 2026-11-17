<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.copy_input_payload -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload at the Input Head

**Claim.** Under the stated hypotheses, the pair consisting of the decoded clock bit read and the tag $2$ if that read is blank, or $0$ otherwise, equals the virtual input payload of $x$ at coordinate $j$.

**Proof.** By the symbol-read formula (Complexity.copy_input_read), the symbol read at head position $j+1$ is the embedded bit at position $j$ when that position lies in the word, and is blank at the endpoint. If $j<|x|$, the read is the embedded bit $x_j$. Decoding it gives $x_j$, the read is nonblank, and because $j$ is neither the left exterior coordinate $-1$ nor the right endpoint $|x|$, the virtual payload tag is $0$. If $j$ is not less than $|x|$, the hypothesis $j\le |x|$ forces $j=|x|$. The read is then blank, so its decoded bit is absent and the tag is $2$, exactly the virtual payload at the right endpoint.

**Key facts.** `Complexity.copy_input_read`.
