<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.stepWith_fixCoin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step After Fixing a Choice Bit

**Claim.** For a finite nondeterministic Turing machine $N$ over the Boolean alphabet, bits $b,b'$, and any configuration $C$ of the machine with choice fixed to $b$, its step using $b'$ agrees with the step of $N$ using $b$.

**Proof.** Split on whether $C$ is already halted. In that case both step operations leave the configuration unchanged. Otherwise $C$ has an active state, and the fixed machine's transition function ignores its supplied choice and uses the transition of $N$ indexed by $b$. The two steps therefore apply the same transition to the same configuration and agree.
