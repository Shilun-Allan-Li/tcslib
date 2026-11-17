<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.exists_good_coins -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Good Shared Randomness String

**Claim.** Under the stated per-input success probability assumption, there is one concatenated random string whose blocks make the majority test correctly decide membership in $L$ for every $n$-bit input.

**Proof.** Put $q=a(n+1)^k$ and $K=36(n+1)$, and for each input $v$ call a block correct when its output-membership answer agrees with whether $v\in L$. The hypothesis gives each block correctness probability at least $2/3$, so the probability that a block is incorrect is at most $1/3=1/2-1/6$. The tail bound for block counts (`randProb_tail_le`) therefore bounds the probability that at least half the $K$ blocks are incorrect by $2(1-4(1/6)^2)^{\lfloor K/2\rfloor}=2(1-1/9)^{\lfloor K/2\rfloor}$. Since $\lfloor K/2\rfloor=18(n+1)$, the exponential estimate (`one_sub_pow_le_half_pow`) makes this at most $2(1/2)^{n+2}=(1/2)^{n+1}$. There are $2^n$ possible inputs, and their total bad-event probability is at most $2^n(1/2)^{n+1}<1$. The avoidance theorem (`exists_forall_not_of_randProb_le`) supplies a concatenation for which no input has at least half incorrect blocks. Finally, the correct and incorrect block counts sum to $K$ (`blockCount_add_not`): if $v\in L$, strictly more than half the blocks answer yes; if $v\notin L$, strictly fewer than half answer yes. These are precisely the two directions of the claimed majority equivalence.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_bool_false`, `Randomized.randProb_tail_le`, `Randomized.one_sub_pow_le_half_pow`, `Randomized.exists_forall_not_of_randProb_le`, `Randomized.blockCount_add_not`.
