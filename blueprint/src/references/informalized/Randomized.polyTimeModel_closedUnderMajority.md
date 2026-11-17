<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.polyTimeModel_closedUnderMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Majority Repetition

**Claim.** For every Boolean predicate $M$ and natural numbers $a,k,a',k'$, if the verifier that returns $M(x,r)$ is efficient in the model, then so is the verifier that returns true when more than half of the first $a'(|x|+1)^{k'}$ consecutive blocks of $r$, each of length $a(|x|+1)^k$, make $M$ return true.

**Proof.** Let $V_1$ be the polynomial-time language witnessing the original verifier's true answers. The language that accepts an encoded pair when the number of accepted blocks, as recognized by the indicator of $V_1$, is strictly more than half the prescribed number of blocks is polynomial-time (Complexity.mem_P_of_blockMajority). Use this language for the new verifier's true answers and its complement for false answers; the complement is polynomial-time by Complexity.compl_mem_P. For a fixed $x,r$, the original verifier's witness equivalence shows, block by block, that its Boolean answer equals the indicator of membership of that block's encoding in $V_1$. Consequently the two vote counts agree, and membership in the constructed language is equivalent to the new majority predicate returning true. Its nonmembership is equivalent to that predicate returning false, giving both required verifier equivalences.

**Key facts.** `Complexity.mem_P_of_blockMajority`, `Complexity.compl_mem_P`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
