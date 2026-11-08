<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_closedUnderAny -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Existential Repetition

**Claim.** For every Boolean predicate $M$ and natural numbers $a,k,a',k'$, if the verifier that returns $M(x,r)$ is efficient in the model, then so is the verifier that returns true when at least one of the first $a'(|x|+1)^{k'}$ consecutive blocks of $r$, each of length $a(|x|+1)^k$, makes $M$ return true.

**Proof.** Let $V_1$ be the polynomial-time language witnessing efficient recognition of the true answers of $M$. The language consisting of encoded pairs $(x,r)$ for which some index below $a'(|x|+1)^{k'}$ has its corresponding block accepted by $V_1$ is polynomial-time (Complexity.mem_P_of_blockAny). Use this as the new verifier's true-language and its complement as the false-language; the complement is polynomial-time by Complexity.compl_mem_P. On a correctly encoded pair, decoding recovers $x$ and $r$. Membership in the constructed language says that some such block's encoding belongs to $V_1$. The original verifier's witness equivalence turns this into acceptance by $M$ on that block, which is exactly the existential repetition predicate. Nonmembership gives the false answer, so both witness equivalences required by the model hold.

**Key facts.** `Complexity.mem_P_of_blockAny`, `Complexity.compl_mem_P`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
