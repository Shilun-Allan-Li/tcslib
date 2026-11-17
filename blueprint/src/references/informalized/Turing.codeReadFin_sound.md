<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadFin_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Unary Reader Soundness

**Claim.** If the bounded unary index reader of bound $n$ succeeds on $x$ with result $(i,r)$, then $x$ is the unary code for $i$ followed by $r$.

**Proof.** Unpack the successful bounded read into a successful unary read of some natural number $j$ and suffix $t$, together with the test that $j<n$. The returned index and suffix are the pair formed from $j$ and $t$, so equality of results identifies them with $i$ and $r$. Unary-reader soundness says that $x$ consists of $j$ ones, then a zero, then $t$ (`Turing.codeReadUnary_sound`). Rewriting $j$ as the value of $i$ gives the required unary code and suffix. If the range test had failed, the bounded reader would have returned no result, contradicting the assumed success.

**Key facts.** `Turing.codeReadUnary_sound`.
