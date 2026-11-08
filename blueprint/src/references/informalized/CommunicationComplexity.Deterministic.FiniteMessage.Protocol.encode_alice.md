<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.encode_alice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary encoding of an Alice message

**Claim.** A finite-alphabet message from Alice can be replaced by a sequence of $\lceil\log_2|\beta|\rceil$ binary queries followed by suitable continuation protocols, preserving the output on every input and giving complexity equal to that query length plus the maximum continuation complexity.

**Proof.** Let $d=\lceil\log_2|\beta|\rceil$. Number the elements of $\beta$ by the integers from $0$ to $|\beta|-1$, and encode each number by its $d$ low-order bits. This encoding is injective: equality of all these bits forces equality of the numbered values, since both values are below $2^d$; the bound $|\beta|\le 2^d$ follows from the defining property of the ceiling logarithm. Alice's $i$th query asks for bit $i$ of the encoding of $f(x)$. For a bit pattern that is an encoding, choose its unique corresponding element $b$ and use $Q(b)$ as the continuation. For a pattern not in the image, use a fixed element $b_0\in\beta$ as a fallback continuation. The tree therefore reaches the continuation indexed by the encoding of $f(x)$, which is $Q(f(x))$ by injectivity, so its output agrees with the desired one. The complete-tree evaluation formula (\texttt{completeTreeAlice\_run}) justifies passing from the query tree to the continuation at the collected pattern. For complexity, the complete-tree complexity formula (\texttt{completeTreeAlice\_complexity}) gives $d$ plus the supremum of continuation complexities over all bit patterns. This supremum equals the supremum over $b\in\beta$: every pattern's continuation is some $Q(b)$, either from decoding or from the fallback, so it is bounded by the supremum over $\beta$; conversely, every $Q(b)$ occurs at the encoding of $b$, so the supremum over $\beta$ is bounded by the one over patterns. The two suprema are equal, giving the stated complexity.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_complexity`.
