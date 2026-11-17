<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.syntaxSuffix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix Condition Tracks Machine Runs

**Claim.** For any state and finite bit string, the syntax suffix condition holds exactly when processing the string from that state ends in state $4$.

**Proof.** Induct on the length of the string, keeping the initial state arbitrary. For the empty string, the suffix condition holds exactly at state $4$ (\texttt{syntaxSuffix\_nil}); processing no bits also leaves the state unchanged, so this is exactly the acceptance condition. For a nonempty string with first bit $b$ and remaining string $x$, the leading-bit characterization rewrites the suffix condition as the condition for $x$ from the state reached by reading $b$ (\texttt{syntaxSuffix\_cons}). The induction hypothesis identifies that with the run on $x$ ending at state $4$. By the definition of the run, this is equivalent to the run on the full string $b::x$ ending at state $4$.

**Key facts.** `Std.Sat.CNF.syntaxSuffix_nil`, `Std.Sat.CNF.syntaxSuffix_cons`.
