<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.InBPP.inBPPAt_23_24 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplified Success Probability

**Claim.** If the verifier model is closed under majority amplification, then any language in its bounded-error class has a verifier whose success probability is at least $23/24$ on every input.

**Proof.** Start with a verifier having success probability at least $2/3$. Apply the concrete majority-amplification construction with parameters $b=5$ and $e=0$ (`amplify_concrete`). It produces an efficient verifier with success probability at least $1-(1/2)^{\mathrm{polyLen}(5,0,n)}$ on inputs of length $n$. Since $\mathrm{polyLen}(5,0,n)=5$, this lower bound is $1-1/32=31/32$, which is at least $23/24$. The same bound applies to both members and nonmembers, yielding the claimed verifier.

**Key facts.** `Randomized.amplify_concrete`.
