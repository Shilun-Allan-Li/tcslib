<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Transducer.lean :: Complexity.transduce_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transducer Output on Concatenated Strings

**Claim.** For binary words $l_1,l_2$, the transducer’s output on their concatenation is the output on $l_1$ from state $q$, followed by the output on $l_2$ from the state reached by folding the transition function over $l_1$ starting at $q$.

**Proof.** Induct on the first word, generalizing the initial state. If it is empty, concatenation leaves the second word unchanged, and folding over the empty word leaves the state equal to $q$, so both sides are the same output. For the inductive step write the first word as $b::l$. Reading its first bit emits the list associated to $o(q,b)$ and changes state to $\delta(q,b)$. Apply the induction hypothesis to the remaining word $l$ with this new state. The fold over $b::l$ is exactly the fold over $l$ starting at $\delta(q,b)$; associativity of list concatenation then groups the emissions as the output on the whole first word followed by that on the second.
