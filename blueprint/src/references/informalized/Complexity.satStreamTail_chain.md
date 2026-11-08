<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamTail_chain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail Output and the Splitting Chain

**Claim.** For literals $a,b$, a clause tail $C$, and cursor $j$, the clause-marker encodings of the splitting chain on $a$, $b::C$, and $j$ form one marker followed by the encodings of $a$ and $b$ and the pending tail output for $C$ at cursor $j$. The returned cursor agrees with that pending tail output.

**Proof.** Induct on the tail clause. When it is empty or has one literal, the splitting chain makes no recursive split; unfolding the definitions shows directly that the sole clause encoding gives the stated marker and literal encodings, with the cursor unchanged. In the remaining case, write the tail as $c::d::C'$. Apply the induction hypothesis to the recursive chain, now with head $(j,\mathrm{false})$, tail $c::d::C'$, and cursor $j+1$. Its output and cursor describe the recursive portion of the chain. Unfolding the definitions, the first clause contributes the encodings of $a$, $b$, and the fresh positive literal $(j,\mathrm{true})$; the recursive head contributes the fresh-variable marker and polarity bits represented in the pending tail output. Associativity of list concatenation puts these pieces in the claimed order. The cursor equality is exactly the recursive cursor equality from the induction hypothesis.
