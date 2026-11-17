<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nans_det -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer After a Deterministic Instruction

**Claim.** A length-$(N+1)$ choice sequence leaves answer $b$ from the given state with deterministic instruction $i$ exactly when a length-$N$ sequence leaves answer $b$ after the corresponding deterministic step.

**Proof.** For the forward direction, take a witnessing sequence of length $N+1$ and write it as its first choice bit followed by a tail of length $N$. The first step of the nondeterministic machine agrees with the deterministic machine’s step because the instruction at this state is deterministic; this is the fact that `nastep_det` supplies. By the decomposition of a run on a cons-list (`narun_cons`), the original sequence’s final recorded answer is therefore the answer obtained by running its tail from the deterministic successor configuration. The tail witnesses the right-hand side. Conversely, given a length-$N$ sequence from that successor, prepend either choice bit, for example false. The same one-step agreement and run decomposition show that the extended sequence has the same final recorded answer.

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_det`.
