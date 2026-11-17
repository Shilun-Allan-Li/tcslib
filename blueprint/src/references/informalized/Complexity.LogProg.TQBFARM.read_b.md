<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.read_b -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Successful Bit Read

**Claim.** If the instruction at $l$ calls the first oracle in whole-input mode with the input-pointer register as its sole argument, the registers of $st$ are bounded by $B$, and the bit of $x$ at position $st.P$ is $b$, then any bounded, precondition-preserving run from the corresponding successor state—$l_1$ when $b$ is true and $l_0$ when $b$ is false—to $c$ can be preceded by starting at $l$ with registers $st$.

**Proof.** Split according to the Boolean value of $b$. If $b$ is false, the false-read result (\texttt{Complexity.LogProg.TQBFARM.read_f}) applies: the oracle call at $l$ takes its negative branch, so the given run from $l_0$ also starts from $l$. If $b$ is true, the true-read result (\texttt{Complexity.LogProg.TQBFARM.read_t}) applies: the call takes its positive branch, and the given run from $l_1$ can likewise be prefixed by that call. In either case the register bound supplies the hypotheses required by the corresponding read result, and the endpoint $c$ is unchanged.

**Key facts.** `Complexity.LogProg.TQBFARM.read_f`, `Complexity.LogProg.TQBFARM.read_t`.
