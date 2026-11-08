<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.syntaxSuffix_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Syntax Suffix After a Leading Bit

**Claim.** For every state, bit, and finite bit string, the suffix condition holds for the bit followed by the string exactly when it holds for the remaining string from the state reached after reading that bit.

**Proof.** Check the six possible states and the two possible leading bits, using the definitions of the suffix condition and the transition. In state $0$, a leading $0$ can only be the final terminator of an empty formula, leaving the empty string; a leading $1$ introduces the first clause, leaving a clause encoding followed by a formula encoding. In state $1$, a leading $0$ marks the end of an empty clause, leaving a formula encoding; a leading $1$ begins a literal, so the remainder has the unary literal prefix and subsequent clause and formula encodings required in state $2$. In state $2$, a leading $0$ completes the unary variable prefix and leaves the bit and clause-plus-formula encodings required in state $3$; a leading $1$ extends that prefix, leaving a state-$2$ suffix. In state $3$, either leading bit is the bit completing the literal, leaving a clause encoding followed by a formula encoding, as required in state $1$. For state $4$, a nonempty string cannot satisfy the condition, and the transitioned state is $5$, whose condition is false. State $5$ is false both before and after the transition. These cases give the claimed equivalence.
