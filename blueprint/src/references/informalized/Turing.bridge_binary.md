<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_binary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary computation by a finite machine

**Claim.** If a partial-recursive program sends the singleton containing the sentinel code of each Boolean string $x$ to the singleton containing the sentinel code of $f(x)$, then a finite Turing machine over the Boolean alphabet computes $f$ in a time depending only on the input length.

**Proof.** For each input string $x$, the compilation result (\texttt{bridge_compiles}) gives a time $t(x)$ at which the bridging machine computes $f(x)$. For each length $n$, define $T(n)$ as the maximum of these times over all Boolean strings of length $n$; equivalently, take the supremum over the finite set of length-$n$ vectors. Since each such string is among the vectors in this set, $t(x)\le T(|x|)$. The monotonicity of computation time (\texttt{ComputesInTime.mono}) therefore shows that the bridging machine computes $f(x)$ at time $T(|x|)$ on every input. The alphabet-reduction theorem (\texttt{FinTM.alphabet_reduction}) converts this machine, whose tape alphabet includes both Boolean input symbols and work symbols, into a finite machine over the Boolean alphabet, with a uniform time bound obtained by multiplying the old bound plus one by a fixed constant. This supplies the required machine and time function.

**Key facts.** `Turing.bridge_compiles`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.alphabet_reduction`.
