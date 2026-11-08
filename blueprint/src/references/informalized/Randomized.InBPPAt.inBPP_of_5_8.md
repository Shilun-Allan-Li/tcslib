<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.InBPPAt.inBPP_of_5_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplifying a Five-Eighths Success Probability

**Claim.** If a verifier model is closed under majority repetition, a language with an efficient verifier achieving success probability at least $5/8$ on every input has an efficient verifier achieving at least $2/3$ on every input.

**Proof.** First weaken the success lower bound from $5/8$ to $1/2+1/8$, which is the same number. Apply the majority-amplification theorem with $K=60$, $\varepsilon=1/8$, and $\eta=1/3$. Its tail bound is satisfied since $2(1-4(1/8)^2)^{30}=2(15/16)^{30}\le1/3$. The resulting verifier succeeds with probability at least $1-\eta=2/3$ on both members and nonmembers. Monotonicity in the success threshold (`InBPPAt.mono`) gives the desired bounded-error class membership.

**Key facts.** `Randomized.InBPPAt.mono`, `Randomized.InBPPAt.amplify`, `Randomized.InBPPAt.mono`.
