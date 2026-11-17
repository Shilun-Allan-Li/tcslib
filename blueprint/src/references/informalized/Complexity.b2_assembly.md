<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_assembly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduler halt to verifier start

**Claim.** If the scheduler configuration $c$ is halted and $|w|=|x\mathbin{+	}u|+2$, running the combined host on $w$ from the guessing configuration built from $c$ and $u$ reaches the verifier phase with its verifier machine initialized on $x$ followed by $u$, the boundary tag set to true, and the specified inherited tape and head data.

**Proof.** Write $y=x\mathbin{+	}u$. The length condition rules out an empty choice word, since it says $|w|=|y|+2$. Thus $w$ begins with a bit followed by a suffix of length $|y|+1$. The first bit takes the host from the guessing configuration to the ready configuration by the halted-scheduler return property (`b2_guess_return`). The ready-state run property (`b2_ready_run`) says that any suffix of length $|y|+1$ then initializes the verifier on $y$, sets the boundary tag to true, and preserves the stated tape and head data. Its hypotheses hold with $j=|y|$, since $j\le |y|$ and the suffix has length $j+1$.

**Key facts.** `Complexity.b2_guess_return`, `Complexity.b2_ready_run`, `Turing.NDTM.runWith_cons`.
