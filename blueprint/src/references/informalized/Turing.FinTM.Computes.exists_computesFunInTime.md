<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Computable.lean :: Turing.FinTM.Computes.exists_computesFunInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A time bound for computed functions

**Claim.** If a finite Turing machine computes a function on every input, then there is a time bound depending only on input length within which it computes that function on every input.

**Proof.** For each input $x$, choose a time $t(x)$ at which the machine halts with output $f(x)$. For each length $n$, define $T(n)$ to be the maximum of these chosen times over all words of length $n$, represented as vectors of length $n$. There are finitely many such vectors because the alphabet is finite, so this maximum exists. Given an input $x$, regard it as a vector of length $|x|$; its chosen time is at most $T(|x|)$ by the defining property of the maximum. Computation time is monotone: a run that has halted with a given output remains a computation with that output at every later time (\texttt{Turing.FinTM.ComputesInTime.mono}). Thus the machine computes $f(x)$ within $T(|x|)$ steps.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
