<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.syntaxSuffix_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Syntax Suffix

**Claim.** The empty bit string satisfies the syntax suffix condition at state $q$ exactly when $q=4$.

**Proof.** Inspect the six states in the definition. State $4$ requires precisely that the string be empty, so its condition holds. In state $0$, a serialized formula always ends in a terminating $0$; in state $1$, a clause encoding followed by a formula encoding contains the clause terminator; in state $2$, the prescribed literal prefix contains a $0$; and in state $3$, the prescribed string begins with a bit. None of these can be empty. State $5$ is false by definition. Hence only state $4$ satisfies the condition on the empty string.
