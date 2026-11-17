<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Tail_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Header Tails

**Claim.** For natural numbers $a,b$ and a finite binary word $w$, taking $a+b$ iterated header tails of $w$ equals taking $a$ iterated header tails and then $b$ more.

**Proof.** Induct on $b$. When $b=0$, the claim is the defining identity for zero iterates. For the successor step, the definition of one more header tail applies the same operation—decode the current word and retain its second component, using the empty word if decoding fails—to both sides. By the induction hypothesis, the words supplied to this final operation agree, so the results agree as well.
