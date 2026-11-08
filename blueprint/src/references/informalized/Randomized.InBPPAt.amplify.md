<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.InBPPAt.amplify -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Amplification

**Claim.** If efficient verifiers are closed under majority repetition and a verifier succeeds with probability at least $1/2+\varepsilon$, where $\varepsilon\ge0$, then repeating it $K$ times and taking a majority yields success at least $1-\eta$ whenever $2(1-4\varepsilon^2)^{\lfloor K/2\rfloor}\le\eta$.

**Proof.** Choose the majority verifier that runs the original verifier on $K$ disjoint blocks, each of length $q=\mathrm{polyLen}(a,k,|x|)$. Its random-string length is $Kq$, and closure under majority makes it efficient. If $x$ is in the language, the original verifier answers correctly with probability at least $1/2+\varepsilon$; equivalently, its probability of answering incorrectly is at most $1/2-\varepsilon$. A wrong majority requires at least half of the blocks to be wrong. The tail bound for the number of such blocks (`randProb_tail_le`) bounds this failure probability by $2(1-4\varepsilon^2)^{\lfloor K/2\rfloor}$, hence by $\eta$. The identity relating a Boolean answer's true and false probabilities (`randProb_bool_false`) and the fact that complementary block counts sum to $K$ (`blockCount_add_not`) translate the majority-error event into this tail event. For inputs outside the language, apply the same tail bound to the event that a block answers true, whose probability is at most $1/2-\varepsilon$. The majority's probability of answering false is consequently at least $1-\eta$ as well. The blockwise event identifications preserve probability (`randProb_congr`); in the nonmember case, inclusion of the majority-error event in the tail event suffices (`randProb_mono`), and complements have probability one minus the event probability (`randProb_not`).

**Key facts.** `Randomized.randProb_bool_false`, `Randomized.randProb_congr`, `Randomized.randProb_tail_le`, `Randomized.blockCount_add_not`, `Randomized.randProb_not`, `Randomized.randProb_mono`.
