<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.FinNDTM.coinBranch_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the selected branch

**Claim.** Running the combined machine first with choice $b$ and then with the word $w$ produces the embedded run of $N_1$ when $b=1$, and the embedded run of $N_0$ when $b=0$.

**Proof.** Unfold the first choice in the run using the decomposition of a run on a nonempty word into its first step followed by the remaining run (`runWith_cons`). The initial-step theorem (`coinBranch_stepWith_init`) identifies that first step with the initial configuration embedded in the branch selected by $b$. Split on $b$: in each case, the branch-preservation theorem for the remaining word (`coinBranch_runWith₀` or `coinBranch_runWith₁`) says that the combined machine's run from that embedded configuration is exactly the embedding of the selected machine's run. These are precisely the two sides of the stated conditional.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.FinNDTM.coinBranch_stepWith_init`, `Turing.FinNDTM.coinBranch_runWith₀`, `Turing.FinNDTM.coinBranch_runWith₁`.
