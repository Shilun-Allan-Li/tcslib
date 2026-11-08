<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clHeaderTail_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Header Tails

**Claim.** For each fixed nonnegative integer $j$, the function sending a Boolean word $z$ to the result of applying the payload projection $j$ times, using the empty word whenever a projection is undefined, is polynomial-time computable.

**Proof.** Proceed by induction on $j$. For $j=0$, the function is the identity, which is polynomial-time computable. For the successor case, the function for $j+1$ first applies the function for $j$, then applies the payload projection, returning the empty word when that projection is undefined. The payload projection has a linear-time implementation, so it is polynomial-time computable; closure under composition with the already computable $j$-fold function proves the successor case.

**Key facts.** `Complexity.polyTimeComputable_id`, `Complexity.clNative_linear`, `Turing.FinTM.computesFunInTime_pairSnd`, `Complexity.PolyTimeComputable.comp`.
