<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Streaming Schedule Computes the Reduction

**Claim.** For every finite bit string $x$, running $|x|+1$ rounds from the startup state emits exactly the string-level SAT-to-3SAT reduction of $x$.

**Proof.** Split according to whether parsing $x$ succeeds. If parsing fails, the specification of the syntax check says it returns false exactly when parsing fails (\texttt{Std.Sat.CNF.syntaxOK_spec}). Thus the startup state has fresh cursor $0$, consumed length $|x|$, and phase $0$. The fallback-run result (\texttt{Complexity.satStreamRun_fallback}) says that this run emits $[0]$, while the fallback-reduction result (\texttt{Complexity.satReduction_fallback}) identifies the reduction output with the serialization of the empty formula, which is $[0]$. If parsing succeeds with formula $\varphi$, the same syntax-check specification makes the startup state $(\varphi.\mathrm{numVars},0,0)$, and decoding recovers $\varphi$. The parser representation theorem (\texttt{Std.Sat.CNF.parse_repr}) gives $x=\operatorname{serialize}(\varphi)$. Applying the streaming schedule for serialized formulas (\texttt{Complexity.satStreamRun_serialize}) now identifies the emitted output with $\operatorname{serialize}(\operatorname{satTransform}(\varphi))$, which is exactly the string-level reduction of $x$.

**Key facts.** `Std.Sat.CNF.syntaxOK_spec`, `Complexity.satReduction_fallback`, `Complexity.satStreamRun_fallback`, `Std.Sat.CNF.parse_repr`, `Complexity.satStreamRun_serialize`.
