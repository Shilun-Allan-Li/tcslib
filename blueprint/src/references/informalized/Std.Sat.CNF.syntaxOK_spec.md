<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNFEncoding.lean :: Std.Sat.CNF.syntaxOK_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Syntax Test Characterizes Parsing

**Claim.** For each finite bit string $x$, the syntax test returns true exactly when exact-consumption parsing of $x$ succeeds.

**Proof.** First, the suffix characterization of the six-state machine identifies the syntax condition at state $0$ with the condition that processing $x$ ends in state $4$ (\texttt{syntaxSuffix\_run}). By the definition of that condition, state $0$ means that $x$ is the serialization of some formula. If $x$ is such a serialization, the encoding-parsing theorem gives successful parsing (\texttt{parse\_serialize}). Conversely, if parsing succeeds with some formula, the parsing reconstruction theorem shows that $x$ is that formula's serialization (\texttt{parse\_repr}). These implications identify the machine's acceptance condition with successful parsing.

**Key facts.** `Std.Sat.CNF.syntaxSuffix_run`, `Std.Sat.CNF.parse_serialize`, `Std.Sat.CNF.parse_repr`.
